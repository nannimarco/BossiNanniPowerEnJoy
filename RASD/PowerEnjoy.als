module powerEnjoy

/**----------------------------------ID------------------------------------**/

abstract sig ID {}{ID in UserID + CarID +ZoneID}

--SetDefinition: Each ID extension is a specified value of a certain signature
sig UserID, CarID, ZoneID extends ID{
}{UserID = User.userID and CarID=Car.carID and ZoneID=Zone.zoneID}

/**-----------------------------BOOLEAN--------------------------------**/
--SetDefinition: The booleans are used only in ParkedCar, FreeCar and ChargingPosition
abstract sig Boolean{
}{Boolean in ChargingPoint.free+CarStatus.chargingBattery}

sig True extends Boolean{
}{#True<=1}

sig False extends Boolean{
}{#False<=1}

/**-----------------------------POSITION--------------------------------**/

--SetDefinition: Each Position is contained in the union of portionMap and contained position
sig Position{
}{Position in Zone.portionMap+Zone.containedPosition}

/**---------------------------------TIME-----------------------------------**/

--SetDefinition: Each time belogns to a Employment
--ValDefinition: There are not negative times
sig Time{
	timeLog: one Int
}{timeLog>=0 and 
		Time in Employment.reservationTime+Employment.startUse+Employment.endUse}

/**--------------------------------SYSTEM---------------------------------**/

--ValDefinition: There is only one system
sig System{
	map: one Map,
	userTable: set User,
	carTable: set Car,
	employmentSet: set Employment
}{#System = 1}

/**----------------------------------CAR-----------------------------------**/

--SetDefinition: Each car is contained in the System car Table
--						 Each car Position belongs to the contained position set of a zone
--ValDefinition: The battery value goes from 0 to 100 in order to identify a percentual
sig Car{
	carID: one CarID,
	carPosition: one Position,
	currentBattery: one Int,
	carStatus: one CarStatus
}{Car in System.carTable
		and carPosition in Zone.containedPosition 
			and currentBattery>=0 and currentBattery<=100}

--Fact Definition: Each car is unique and this unicity is specified by a different ID
fact carUnique{
	all disj c1, c2: Car| no c1.carID & c2.carID
}

--Fact Definition: There is a univocal correspondation between a Car and a Status,
--							each Car has a different Status
fact correspondingStatusCar{
	all disj c1,c2: Car | no c1.carStatus & c2.carStatus
}

--Fact Definition: There aren't two Car in the same Position
fact noCarSamePosition{
	no disj c1,c2 : Car | c1.carPosition = c2.carPosition
}

--FactDefinition: If a Car is Free it couldn't have an employment
fact noFreeCarImployed{
	all c:Car| c.carStatus in FreeCar iff
		no e:Employment | e.carEm= c
}

--FactDefintion: A reserved Car implies an employment with no startUse and endUse 
fact ReservedCarImployed{
	all c:Car| c.carStatus in ReservedCar iff
		one e:Employment | e.carEm= c and #e.startUse=0 and #e.endUse=0
}

--FactDefintion: An occupied Car implies an employment with a startUse but no endUse 
fact OccupiedCarImployed{
	all c:Car| c.carStatus in OccupiedCar iff
		one e:Employment | e.carEm= c and #e.startUse=1 and #e.endUse=0
}

--FactDefintion: A parked Car implies an employment with a startUse and endUse 
fact ParkedCarImployed{
	all c:Car| c.carStatus in ParkedCar iff
		one e:Employment | e.carEm= c and #e.startUse=1 and #e.endUse=1
}

--FactDefinition: A ParkedCar can be charged only in ChargingPoint
fact ParkedAndCharging{
	all c:Car | all ch: ChargingPoint | c.carStatus in ParkedCar+FreeCar+ReservedCar
		and c.carPosition in ch.chargingPosition 
			implies (c.carStatus.chargingBattery = True or c.carStatus.chargingBattery = False) 
				else c.carStatus.chargingBattery = False
}

/**------------------------------CARSTATUS--------------------------------**/

--SetDefinition: Each CarStatus belongs to a Car
abstract sig CarStatus {
	chargingBattery: one Boolean
}{CarStatus = Car.carStatus}

sig FreeCar extends CarStatus{
}

sig ReservedCar extends CarStatus{
}{}

sig OccupiedCar extends CarStatus{
}{chargingBattery = False}
 
sig ParkedCar extends CarStatus{
}


/**---------------------------------USER-----------------------------------**/


--SetDefinition: Each User belongs to the System User Table
--						 Each User Position belongs to the contained position set of a zone
sig User {
	userID : one UserID,
	userPosition: one Position,
	userStatus: one UserStatus
}{User in System.userTable 
		and userPosition in Zone.containedPosition}

--FactDefinition: Each User is Unique
fact userAreUnique{
	all disj u1, u2: User| no u1.userID&u2.userID
}

--FactDefinition: Each User has a different Status
fact correspondingStatusCar{
	all disj u1,u2: User | no u1.userStatus & u2.userStatus
}

--FactDefinition: If a registred User couldn't have an employment
fact noRegistredUserImployed{
	all u:User| u.userStatus in RegistredUser iff
		no e:Employment | e.userEm= u
}

--FactDefinition: A user is reserving a car only if there is a employment with his name
fact ReservingUserImployed{
	all u:User| u.userStatus in ReservingUser iff
		one e:Employment | e.userEm=u  and #e.startUse=0 and #e.endUse=0
}

--FactDefinition: A user is reserving a car only if there is a employment with his name
-- 						  and he'using the car
fact OccupiedUserImployed{
	all u:User| u.userStatus in OccupiedUser iff
		one e:Employment | e.userEm=u  and #e.startUse=1 and #e.endUse=0
}

--FactDefinition: A user is reserving a car only if there is a employment with his name
--						  and he's completed the employment
fact PayingUserImployed{
	all u:User| u.userStatus in PayingUser iff
		one e:Employment | e.userEm=u and #e.startUse=1 and #e.endUse=1
}

/**----------------------------USERSTATUS-------------------------------**/

--SetDefinition: Each UserStatus belongs to a User
abstract sig UserStatus {
}{UserStatus= User.userStatus} 

sig RegistredUser extends UserStatus{
}

sig ReservingUser extends UserStatus{
}
 
sig OccupiedUser extends UserStatus{
}
 
sig PayingUser extends UserStatus{
}

/**----------------------------------MAP-----------------------------------**/

--SetDefinition: A map belongs to a System
sig Map{
	zoneSet: some SafeZone,
	borderSet: set BorderZone
}{Map in System.map}

/**---------------------------------ZONE-----------------------------------**/

--SetDefinition: Each zone is contained in zoneSet or borderSet
--FactDefinition: Each zone is delimited by at least three position (triangle)
abstract sig Zone{
	zoneID: one ZoneID,
	portionMap: some Position,
	containedPosition: set Position
}{ Zone in Map.zoneSet+Map.borderSet and #portionMap>=3}

--SigDefinition: A SafeZone could have a charging point 
sig SafeZone extends Zone{
	powerStation: lone PowerGridStation,
}

--SigDefinition: A borderZone is a zone where a car can go but where it can't be parked
sig BorderZone extends Zone{}



--FactDefinition: There aren't intersection of position between two Zones
-- 						  Each zone is unique, so they have a different ID
fact noDataIntersection{
	all disj z1,z2: Zone|  no z1.portionMap & z2.portionMap 
		and no z1.containedPosition & z2.containedPosition
				and no z1.containedPosition & z2.portionMap
					and  no z1.zoneID & z2.zoneID
}

--FactDefintion: There is no intersection between containedPositionSet and portionMap set
fact portionMapContainedPositionDisjointed{
	all z: Zone| no z.portionMap & z.containedPosition
}


/**-----------------------POWERGRIDSTATION---------------------------**/
--SetDefinition: Each PowerGridStation is contained in a SafeZone
sig PowerGridStation{
	chargingGrid: some ChargingPoint
}{PowerGridStation in SafeZone.powerStation}

/**--------------------------CHARGINGPOINT-----------------------------**/

--SetDefinition: Each ChargingPoint is contained in a PowerGridStation
sig ChargingPoint{
	free: one Boolean,
	chargingPosition: one Position 
}{ChargingPoint in PowerGridStation.chargingGrid and 
		chargingPosition in SafeZone.containedPosition}

--FactDefinition: Every ChargingPoint is contained in the SafeZone that has its
-- 						  own PowerGridStation
fact stationPointPositionCorrespondation{
	 all z: SafeZone| all c: ChargingPoint|
		c.chargingPosition in  z.containedPosition 
			iff c in z.powerStation.chargingGrid 
}

--FactDefinition: If there is a Car in the same position of the ChargingPoint 
--                        we assume this chargingPoint occupied
fact notFreeMeansOccupiedByACar{
	all ca:Car | all ch: ChargingPoint|  
		 ca.carPosition = ch.chargingPosition  iff ch.free=False and
		!(ca.carPosition = ch.chargingPosition)  iff ch.free=True
}

--FactDefinitoin: Each Charging Point has a unique position
fact noChargingPositionShared{
	all disj c1,c2: ChargingPoint| no c1.chargingPosition & c2.chargingPosition
}

/**----------------------------EMPLOYMENT-------------------------------**/

--SetDefinition: Each Employment belongs to the Employment Set
--ValDefinition: reservation Time is anterior of start Use Time
--						startUseTime is anterior of end Use Time 
sig Employment{
	userEm: one User,
	carEm: one Car,
	reservationTime: one Time,
	startUse: lone Time,
	endUse: lone Time
}{Employment in System.employmentSet
		reservationTime.timeLog <= startUse.timeLog 
			and startUse.timeLog <=endUse.timeLog}

--FactDefiniton: Each employment is unique and there aren't two employments 
--						  that involve the same user or car 
fact employmentUnicity{
	no disj e1,e2 : Employment | e1.userEm = e2.userEm or
		e1.carEm = e2.carEm
}

/**----------------------------ASSERTIONS-------------------------------**/

--AssertDefintion: if a Car has a FreeStatus then it cannot have an employment
assert oneCarOneEmpoyment{
	all c:Car| !(c.carStatus in FreeCar) implies 
		(one e:Employment| e.carEm = c)
}

--AssertDefintion: if a User has a RegistredUser then it cannot have an employment
assert oneUserOneEmployment{
	all u:User| !(u.userStatus in RegistredUser) implies 
		(one e:Employment| e.userEm = u)
}

--AssertDefinition: Each reservation corresponds to a specified carStatus and 
--                           a userStatus for example if a reservation is completed (it has
--                           a endUse Time) the car is parked and the user is paying
assert relationBetweenCarUserAndEmployment{
	all e:Employment | 
		(#e.reservationTime=1 implies 
			e.carEm.carStatus in ReservedCar+OccupiedCar+ParkedCar and
			e.userEm.userStatus  in ReservingUser+OccupiedUser+PayingUser) and
		(#e.reservationTime=1 and #e.startUse=1 implies
			e.carEm.carStatus in OccupiedCar+ParkedCar and
			e.userEm.userStatus  in OccupiedUser+PayingUser) and
		(#e.reservationTime=1 and #e.startUse=1 and #e.endUse=1 implies
			e.carEm.carStatus in ParkedCar and
			e.userEm.userStatus in PayingUser)
}

--AssertDefinition: This assertion verifies the correct number of signatures of each
--							 possible representation
assert correctQuantities{
	#CarStatus=#Car
	#UserStatus=#User
	#Position >= #Zone+ #Zone+ #Zone+ #containedPosition
	#Boolean <= 2
	#Employment <= #Car
	#Employment <= #User
	#Time >= #Employment
}

check oneCarOneEmpoyment
check oneUserOneEmployment
check relationBetweenCarUserAndEmployment
check correctQuantities

pred show[]{
#User>0
#BorderZone>0
#SafeZone>0
#Car>0
#Employment>0
#PowerGridStation>0
}

run show for 8
