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
	status: one TaxiDriverStatus,
	taxi: lone Taxi,
	queuePosition: lone Int,
	zone: lone Zone
}{
	queuePosition > 0
	//Zone and queuePosition are both defined or neither
	status = OFFLINE implies (#queuePosition = 0 and	#zone = 0 and #taxi = 0 )
	status = AVAILABLE implies (#queuePosition = 1 and #zone = 1 and #taxi = 1)
	status = BUSY implies (#queuePosition = 0 and #zone = 0 and #taxi = 1)
}

abstract sig TaxiDriverStatus {}
sig AVAILABLE extends TaxiDriverStatus {}
sig BUSY extends TaxiDriverStatus {}
sig OFFLINE extends TaxiDriverStatus {}

sig Zone {}

sig Ride{
	driver: one TaxiDriver,
	taxi: one Taxi,
	routes: some Route,
}

sig Route{
	client: one Client,
	numberOfPeople: one Int,
	reservationDate: lone Int,
	beginDate: lone Int,
	endDate: lone Int,
	ride: lone Ride,
	isShared: one Bool,
	isReserved: one Bool,
	status: one RouteStatus
}{
	numberOfPeople > 0 && numberOfPeople =< 4
	reservationDate > 0
	reservationDate < beginDate
	beginDate < endDate
}

abstract sig RouteStatus {}
sig NOT_ALLOCATED extends RouteStatus {}
sig WAITING extends RouteStatus {}
sig IN_PROCESS extends RouteStatus {}
sig COMPLETED extends RouteStatus {}

sig Taxi {
	numberOfSeats: one Int,
	drivers: some TaxiDriver
}{
	numberOfSeats > 0
}

// FACTS
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

//Two working driver can't use the same taxi
fact workingNoSameTaxi{
	all d: TaxiDriver |
		(d.status = BUSY or d.status = AVAILABLE)
		implies
		(no disj r1,r2: Ride | r1.taxi = r2.taxi)
}

//A taxi driver is busy during the entire ride.
fact busyDuringRide {
	all d: TaxiDriver, r: Ride, rt: Route |
		(r.driver = d and rt in r.routes and rt.status != COMPLETED)
		implies
		d.status = BUSY
}

//If the route is reserved there must be a reservationDate, beginDate and isReserved = True
fact notAllocatedRide{
	all rt:Route | rt.status=NOT_ALLOCATED 
	implies (#rt.reservationDate=1 and #rt.beginDate=1 and rt.isReserved=True)
}

//If the route is reserved and allocated there must be a 
//reservationDate, beginDate, isReserved = True and a ride
fact allocatedRide{
	all rt:Route | (rt.status=WAITING and rt.isReserved=True)
	implies (#rt.reservationDate=1 and #rt.beginDate=1 and rt.isReserved=True and #rt.ride=1)
}

//If the route is reserved and allocated there must be a beginDate and a ride
fact waitingRide{
	all rt:Route | rt.status=WAITING
	implies (#rt.beginDate=1 and #rt.ride=1)
}

//beginDate and associated ride are recorded at the beginning of the ride
fact beginningRide{
	all rt:Route | rt.status=IN_PROCESS
	implies (#rt.beginDate=1 and #rt.ride=1)
}

//endDate is recorded at the end of the ride
fact endingRide{
	all rt:Route | rt.status=COMPLETED 
	implies (#rt.beginDate=1 and #rt.endDate=1 and #rt.ride=1)
}

//The same passenger can't have more than one concurrent rides.
fact OneConcurrentRidePerPassenger {
	all c: Client, disj rt1,rt2: Route | 
		(rt1.client = c and rt2.client = c)
		implies
		rt1.endDate < rt2.beginDate
}

//The same taxi driver can't have more than one concurrent rides.
fact OneConcurrentRidePerDriver {
	all d: TaxiDriver, disj r1, r2: Ride, rt1,rt2: Route | 
		(r1.driver = d and r2.driver = d and  rt1.ride = r1 and rt2.ride = r2)
		implies
		rt1.endDate < rt2.beginDate
}

//The same taxi can't have more than one concurrent rides
fact OneConcurrentRidePerTaxi {
	all disj r1, r2: Ride, rt1,rt2: Route | 
		(rt1.ride = r1 and rt2.ride = r2 and r1.taxi = r2.taxi)
		implies
		rt1.endDate < rt2.beginDate
}

//All clients that take part in a shared ride want to do a shared ride
fact isSharedConsistency{
	no r: Ride | some disj rt1, rt2: Route | rt1 in r.routes and rt2 in r.routes and rt1.isShared = False
}

//If a taxi driver use a taxi in a ride that taxi has to be associated to the taxi driver
fact driverUsesOnlyHisTaxis{
	all r: Ride | no t: Taxi | r.taxi = t and r.driver not in t.drivers
}

fact routeConsistency{
	//A route can be connected at only one ride
	all disj r1,r2: Ride | no rt: Route | rt in r1.routes and rt in r2.routes
	//A route is connected at a ride iff it appears in his routes
	all  r: Ride, rt: Route |
	rt in r.routes
	<=> 
	rt.ride = r
}

fact PeopleNumberConsistency{
	//If a ride is done by N people the taxi they use must at least have N numberOfSeats
	all t: Taxi | no r: Ride | t = r.taxi and sum r.routes.numberOfPeople > t.numberOfSeats
}

fact positionConsistency{
	//Zone positions must be start from 1
	all z: Zone | (no d: TaxiDriver | d.zone = z) or (one d: TaxiDriver | d.zone = z and d.queuePosition = 1) 
	or (all d1: TaxiDriver | one d2: TaxiDriver | d1.zone = z and 
		d2.zone = z and d1.queuePosition != 1 and d1.queuePosition = d2.queuePosition + 1)	
	//Zone positions must be consecutive (every number must have a predecessor)
	all disj d1, d2: TaxiDriver | d1.zone = d2.zone  => d1.queuePosition != d2.queuePosition
}

// ASSERTIONS
// To verify whether there is a counter example uncomment the "check" part under each assertion
assert noConfirmedUser{
	no u: User | u.emailConfirmed = False
}
//check noConfirmedUser

assert noConfirmedClient{
	no c: Client | c.emailConfirmed = False and ((some cc: CreditCard | cc.owner = c) or (some rt: Route | rt.client = c))
}
//check noConfirmedClient

assert noConfirmedDriver{
	no d: TaxiDriver | d.emailConfirmed = False and 
	(#d.zone = 1 or (some t: Taxi | d in t.drivers) or (some r: Ride | r.driver = d) or d.status = OFFLINE)
}
//check noConfirmedDriver

assert offlineDriverInQueue{
	no d: TaxiDriver | d.status = OFFLINE and (#d.zone = 1 or #d.taxi = 1 or (some r: Ride | r.driver = d))
}
//check offlineDriverInQueue

assert offlineDriver{
	no d: TaxiDriver | d.status = OFFLINE
}
//check offlineDriver

assert waitingDriverInQueue{
	no rt: Route | rt.status = WAITING and (no r: Ride | r = rt.ride)
}
//check waitingDriverInQueue

assert sharedRide{
	no r: Ride | #r.routes > 1
}
//check sharedRide 

assert driverNoTaxi{
	no d: TaxiDriver | all t: Taxi | d not in t.drivers
}
//check driverNoTaxi

assert No2TaxiInTheSameZone{
	no z: Zone | one d: TaxiDriver | d.zone = z and d.queuePosition = 2
}
//check No2TaxiInTheSameZone

// COMMANDS
pred show(){
	#Client > 1
	#Ride > 1
	#TaxiDriver > 1
	#{x: Route | x.isShared = True} > 1
	#OFFLINE =< 1
	#AVAILABLE =< 1
	#BUSY =< 1
	#NOT_ALLOCATED =< 1
	#WAITING =< 1
	#IN_PROCESS =< 1
	#COMPLETED =< 1
}
run show for 4