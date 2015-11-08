// Defines Bool, True, False
open util/boolean

//SIGNATURES
abstract sig User {
	emailConfirmed: one Bool
}

sig Client extends User {}

sig CreditCard {
	owner: some Client
}

sig TaxiDriver extends User {
	status: one TaxiDriverStatus
}	

abstract sig TaxiDriverStatus {}
sig AVAILABLE extends TaxiDriverStatus {}
sig BUSY extends TaxiDriverStatus {}
sig OFFLINE extends TaxiDriverStatus {}

sig Zone {
	queue: one TaxiQueue
}

sig TaxiQueue {
	zone: one Zone,
	drivers: set TaxiDriver,
	taxis: set Taxi
}{
	//A taxi per driver
	#drivers = #taxis
}

sig Ride{
	driver: one TaxiDriver,
	taxi: one Taxi,
	routes: some Route,
}

sig Route{
	client: one Client,
	ride: lone Ride,
	isShared: one Bool,
	isReserved: one Bool,
	status: one RouteStatus
}

abstract sig RouteStatus {}
sig NOT_ALLOCATED extends RouteStatus {}
sig WAITING extends RouteStatus {}
sig ON_BOARD extends RouteStatus {}
sig COMPLETED extends RouteStatus {}

sig Taxi {
	drivers: some TaxiDriver
}

//**********************************************FACTS**********************************************
//USER REGISTRATION STATUS CHECK
//A client can do something only if confirmed
fact activeClientIsConfirmed{
	all c: Client | 
		c.emailConfirmed = False 
		implies
		((no cc: CreditCard | cc.owner = c) and (no rt: Route | rt.client = c))
}

//A taxi driver can do something only if confirmed
fact activeTaxiDriverIsConfirmed{
	all d: TaxiDriver | 
		d.emailConfirmed = False 
		implies
		((no t: Taxi | d in t.drivers) and (no r: Ride | r.driver = d) and d.status = OFFLINE)
}

//DRIVER STATUS CHECK
//OFFLINE taxi driver are not in a queue
fact offlineDriverNotInQueue{
	all d: TaxiDriver | all q: TaxiQueue | 
		d.status = OFFLINE
		implies
		d not in q.drivers  
}

//BUSY taxi driver are not in a queue
fact busyDriverNotInQueue{
	all d: TaxiDriver | all q: TaxiQueue | 
		d.status = BUSY
		implies
		d not in q.drivers
}

//A BUSY driver has active route
fact busyDriverHasACurrentRide{
	all d: TaxiDriver, r: Ride, rt:Route | 
		(d.status = BUSY and r.driver = d and rt in r.routes)
		implies
		(rt.status = WAITING or rt.status = ON_BOARD)
}

//A BUSY driver has at least a ride
fact busyDriverOneRide{
	no d: TaxiDriver | d.status = BUSY and (no r: Ride | r.driver = d)
}

//AVAILABE taxi driver are in a queue
fact availableDriverInQueue{
	all d: TaxiDriver | one q: TaxiQueue | 
		d.status = AVAILABLE
		implies
		d in q.drivers  
}

//Taxi driver in a queue are AVAILABLE
fact driverInQueueAvailable{
	all d: TaxiDriver | one q: TaxiQueue | 
		d in q.drivers 
		implies
		d.status = AVAILABLE 
}

//ROUTE STATUS CHECK
//A route in RESERVED_NOT_ALLOCATED state can't be connected to a ride
fact notAllocatedRouteNoRide{
	all rt: Route | no r: Ride | rt in r.routes and rt.status = NOT_ALLOCATED
}

//A route in WAITING, ON_BOARD or COMPLETED state is connected to a ride
fact allocatedRouteRide{
	all rt: Route | 
		(rt.status = WAITING or rt.status = ON_BOARD or rt.status = COMPLETED)
		implies
		(one r: Ride | rt in r.routes)
}

// If a taxi driver has not completed a ride, he is busy
fact busyDuringRide {
	all d: TaxiDriver, r: Ride, rt: Route |
		(r.driver = d and rt in r.routes and rt.status != COMPLETED)
		implies
		d.status = BUSY
}

//SHARED ROUTE CHECK
//All clients that take part in a shared ride want to do a shared ride
fact isSharedConsistency{
	no r: Ride | some disj rt1, rt2: Route | rt1 in r.routes and rt2 in r.routes and rt1.isShared = False
}

//In a shared ride a route can't be WAITING if the others are RESERVED_NOT_ALLOCATED
//It's obvious since a RESERVED_NOT_ALLOCATED route can't be connected at a ride

//In a shared ride a route can't be ON_BOARD if the others are RESERVED_NOT_ALLOCATED
//It's obvious since a RESERVED_NOT_ALLOCATED route can't be connected at a ride

//In a shared ride a route can't be COMPLETED if the others are RESERVED_NOT_ALLOCATED or WAITING
//It's obvious if RESERVED_NOT_ALLOCATED route can't be connected at a ride, but not for WAITING
fact sharedRideWithOneCompleted{
	all disj rt1, rt2: Route | no r: Ride |  rt1 in r.routes and rt2 in r.routes and rt1.status = COMPLETED and rt2.status = WAITING
}

//TAXI CHECK
//Two working driver cant use the same taxi
fact workingNoSameTaxi{
	all d: TaxiDriver |
		(d.status = BUSY or d.status = AVAILABLE)
		implies
		(no disj r1,r2: Ride | r1.taxi = r2.taxi)
}

//A taxi can't be used by a driver in a queue and a ride not completed
fact taxiUsedOnlyByOneDriver{
	all r: Ride, rt: Route, q: TaxiQueue | no t: Taxi | t in q.taxis and r.taxi = t and rt in r.routes and (rt.status = WAITING or rt.status = ON_BOARD)
}

//If a taxi driver use a taxi in a ride that taxi has to be associated to the taxi driver
fact driverUsesOnlyHisTaxis{
	//Each driver has used in rides only his/her taxi
	all r: Ride | no t: Taxi | r.taxi = t and r.driver not in t.drivers
	//Each available driver has at least one of his/her own taxi in the queue he/she is in
	all q: TaxiQueue | no d: TaxiDriver | d in q.drivers and (no t: Taxi | t in q.taxis and d in t.drivers)
}

//ROUTE CHECK
fact routeConsistency{
	//A route can be connected at only one ride
	all disj r1,r2: Ride | no rt: Route | rt in r1.routes and rt in r2.routes
	//A route is connected at a ride iff it appears in his routes
	all  r: Ride, rt: Route |
	rt in r.routes
	<=> 
	rt.ride = r
	//Only a route can be associated to the same client in a ride
	all r: Ride | all disj rt1, rt2: Route | no c: Client | rt1 in r.routes and rt2 in r.routes and rt1.client = c and rt2.client = c
}

//A client can't have more than one current route
fact clientOneCurrentRoute{
	all disj rt1, rt2: Route | no c: Client | rt1.client = c and rt2.client = c and (rt1.status = WAITING or rt1.status = ON_BOARD) and (rt2.status = WAITING or rt2.status = ON_BOARD)
}

//A driver cant have more than one current ride
fact driverOneCurrentRide{
	all disj r1, r2: Ride | all rt1, rt2: Route | no d: TaxiDriver | rt1 in r1.routes and rt2 in r2.routes and r1.driver = d and r2.driver = d and (rt1.status = WAITING or rt1.status = ON_BOARD) and (rt2.status = WAITING or rt2.status = ON_BOARD)
}

//ZONE-QUEUE CHECK
//Each zone is connected with the queue that is related to it
fact zone_queue_relation {
	all z: Zone, q: TaxiQueue | 
		z.queue = q 
		iff
		q.zone = z
}

//Each driver can be in only one queue
fact driver_queue_relation{
	all disj q1,q2: TaxiQueue | no d: TaxiDriver | d in q1.drivers and d in q2.drivers
}

//Each taxi can be in only one queue
fact taxi_queue_relation{
	all disj q1,q2: TaxiQueue | no t: Taxi | t in q1.taxis and t in q2.taxis
}

//A taxi can be in a queue only if one of its owners is in it
fact taxi_driver_queue_relation{
	all q: TaxiQueue | no t: Taxi | t in q.taxis and (no d: TaxiDriver | d in q.drivers and d in t.drivers)
}

//***********************************************ASSERTIONS*******************************************
assert noConfirmedClientWithSomeCCOrRoute{
	no c: Client | c.emailConfirmed = False and ((some cc: CreditCard | cc.owner = c) or (some rt: Route | rt.client = c))
}
check noConfirmedClientWithSomeCCOrRoute

assert noConfirmedDriverNotOFFLINEOrWithSomeRide{
	no d: TaxiDriver | d.emailConfirmed = False and (d.status = AVAILABLE or d.status = BUSY or (some r: Ride | r.driver = d))
}
check noConfirmedDriverNotOFFLINEOrWithSomeRide

assert busyDriverInQueue{
	no d: TaxiDriver | d.status = BUSY and (one q: TaxiQueue | d in q.drivers)
}
check busyDriverInQueue

assert allocatedRouteNotAllocate{
	no rt: Route | (rt.status = WAITING or rt.status = ON_BOARD or rt.status = COMPLETED) and (no r: Ride | r = rt.ride)
}
check allocatedRouteNotAllocate

assert driverNoTaxiAndAvailableOrRide{
	all d: TaxiDriver |
		(d.status = AVAILABLE or d.status = BUSY or ((some r: Ride | r.driver = d)))
		implies
		(some t: Taxi | d in t.drivers)
}
check driverNoTaxiAndAvailableOrRide

assert sameClientmoreRouteInSameRide{
	all r: Ride | all disj rt1,rt2: Route |	no c: Client |  rt1 in r.routes and rt2 in r.routes and rt1.client = c and rt2.client = c
}
check sameClientmoreRouteInSameRide

assert notAllocatedRouteAllocated{
	no rt: Route | rt.status = NOT_ALLOCATED and (one r: Ride | r = rt.ride)
}
check notAllocatedRouteAllocated

assert clientOneWaitingAndAtLeastOneCompleted{
	all r: Ride | all disj rt1,rt2: Route | no c: Client | rt1 in r.routes and rt2 in r.routes and rt1.client = c and rt2.client = c and rt1.status = WAITING and rt2.status = COMPLETED
}
check clientOneWaitingAndAtLeastOneCompleted

assert moreThanOneRidePerDriverOneOfThemNotCompleted{
	all disj r1,r2: Ride | all rt1, rt2: Route | no d: TaxiDriver |  rt1 in r1.routes and rt2 in r2.routes and r1.driver = d and r2.driver = d and (rt1.status = WAITING or rt1.status = ON_BOARD)
}
check moreThanOneRidePerDriverOneOfThemNotCompleted

assert busyDriverNoCurrentRide{
	no d: TaxiDriver | some r: Ride, rt: Route | d.status = BUSY and r.driver = d and rt in r.routes and rt.status = NOT_ALLOCATED and rt.status = COMPLETED
}
check busyDriverNoCurrentRide

assert notSharedRideShared{
	all r: Ride | all disj rt1,rt2: Route| 
		(rt1 in r.routes and rt2 in r.routes)
		implies
		rt1.isShared = True
}
check notSharedRideShared

// COMMANDS
pred show(){
	//At least one shared ride
	some r: Ride | some disj rt1, rt2: Route | rt1 in r.routes and rt2 in r.routes
	#{rt: Route | rt.status = NOT_ALLOCATED} > 0
	#{rt: Route | rt.status = WAITING} > 0
	#{rt: Route | rt.status = ON_BOARD} > 0
	#{rt: Route | rt.status = COMPLETED} > 0
	#{d: TaxiDriver | d.status = AVAILABLE} > 1
	#{d: TaxiDriver | d.status = BUSY} > 1
	#{d: TaxiDriver | d.status = OFFLINE} > 0
}
run show for 7
