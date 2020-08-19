/*********************************************
 * OPL 12.6.0.0 Model
 * Author: Meysam Zamani Forooshani
 * Creation Date: Apr 5, 2019 at 10:47:26 AM
 *********************************************/

 int nClasses = ...;
 int nOptions = ...;
 range O = 1..nOptions;
 range C = 1..nClasses;
 
 int carsOfClass[c in C] = ...;
 int classOption[c in C][o in O] = ...;              
 int m[o in O] = ...;
 int k[o in O] = ...;

 int nPositions; 
 execute {
 	nPositions = 0;
 	for (var c = 1; c <= nClasses; ++c)
 		nPositions += carsOfClass[c];
 }
 
 range P = 1..nPositions; 
 // IMPORTANT HINT!!!!!!
 // A position p in P is a possible starting point of a window for option o iff p + k[o] - 1 <= nPositions.
 // The window itself is [ p...(p+k[o]-1) ]
 
 dvar boolean pc[p in P][c in C];
 dvar boolean po[p in P][o in O];
 
/*
 Variables used in the first version:
 
 dvar int classAt[p in P];
 dvar boolean changeAt[p in P];
 dvar boolean aux[p in P];
 dvar boolean shortChangeAt[p in P];
*/
 
 
 minimize sum(p in 2..(nPositions-1), c in C) ((pc[p][c] == 1) && (pc[p-1][c] == 0) && (pc[p+1][c] == 0));
  
 subject to {
 	// All the cars of each class are assigned to some position
 	forall(c in C)
 		sum(p in P) pc[p][c] == carsOfClass[c];
 	  
 	// Each position has one car assigned
 	forall(p in P)
 	 	sum(c in C) pc[p][c] == 1;
 	 	
 	// The po variables reflect the current pc values
 	forall(p in P)
	 	forall(c in C)
	 	  	forall(o in O : classOption[c][o] == 1)
	 	  	  	pc[p][c] <= po[p][o];

 	// The window constraint is satisfied
 	forall(o in O)
 	  	forall(w in 1..(nPositions - k[o] + 1))
 	  		sum(p in w..(w + k[o] - 1)) po[p][o] <= m[o];

	/*
	First version when I didn't know that boolean operators were already offered by OPL:
	
 	// To get the class at each position  		
 	forall(p in P)
 	  	classAt[p] == sum(c in C) c * pc[p][c];
 	  	
 	// To count the changes of classes
 	forall(p in 1..(nPositions-1)) {
 		classAt[p] - classAt[p+1] >= -nClasses * changeAt[p];
 		classAt[p] - classAt[p+1] <= nClasses * changeAt[p];
 		
 		classAt[p] - classAt[p+1] >= changeAt[p] - (nClasses + 1) * aux[p];
 		classAt[p] - classAt[p+1] <= -changeAt[p] + (nClasses + 1) * (1 - aux[p]);
 	}
 	
 	// To count the short changes of classes
 	forall(p in 1..(nPositions-2)) {
 		shortChangeAt[p] >= changeAt[p] + changeAt[p+1] - 1;
 		shortChangeAt[p] <= changeAt[p];
 		shortChangeAt[p] <= changeAt[p+1];
 	}
 	*/
 }
 
 execute {
  	var solution = new Array(1+nPositions);
 	write("SEQUENCE OF CLASSES: ");
 	for (var p = 1; p <= nPositions; ++p) { 	
 		var placed = 0; 
 		var cl;
 		for (var c = 1; c <= nClasses; ++c) if (pc[p][c] == 1) {++placed; cl = c;}
 		if (placed == 0) {writeln("ERROR: In position " + p + " there is no car"); stop();}
 		else if (placed > 1) {writeln("ERROR: In position " + p + " there is more than one car");stop();}
 		else {solution[p] = cl; write(cl + " ");} 		 
 	}
 	writeln();writeln();
 	for (var o = 1; o <= nOptions; ++o) {
 	 	
 		var violations = 0;
 	 	var solOpt = new Array(1+nPositions);
 		write("OPTION " + o + ":            ");
 		for (var p = 1; p <= nPositions; ++p) { 		 	 	
 			if (classOption[solution[p]][o] == 1) {write("X "); solOpt[p] = 1;}
 			else {write(". "); solOpt[p] = 0;}
        }    		
 		
 		for (p = 1; p + k[o] - 1 <= nPositions; ++p) {
 			placed = 0;
 			for (var pp = p; pp <= p + k[o] - 1; ++pp) {
 				if (solOpt[pp] == 1) ++placed;
  			} 			 			
 			if (placed > m[o]) { 			 			
 				if (violations == 0) write("\tViolations in windows: ");
 				++violations;
 				write("[" + p  + "..." + (p + k[o] - 1) + "] ");
   			} 				 			 		 		
 		}
 		
 		writeln();
 	} 		 		 	
 	
 }  
 
 