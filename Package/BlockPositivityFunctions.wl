(* ::Package:: *)

BeginPackage["BlockPositivityFunctions`"];





(*1. Functions to test things, i.e. To generate polynomials/matrices etc.*)

(*Function generating random rational numbers from two integers*)
randomRational[maxNumerator_,maxDenominator_]:=RandomInteger[{-maxNumerator,maxNumerator}]/RandomInteger[{1,maxDenominator}]

(*Function needed to convert a list of coefficients into a polynomial*)
polyForm[coeff_,var_:t]:=Sum[coeff[[i]]*var^(i-1),{i,1,Length[coeff]}]

(*Function generating random polynomials with rational coefficients*)
randomPolynomial[degree_Integer,maxNumerator_Integer:1000,maxDenominator_Integer:1000,var_:t]:=Module[{coefficients},coefficients=Table[randomRational[maxNumerator,maxDenominator],{degree+1}];
polyForm[coefficients,var]]

(*Function to generate a random Hermitian matrix with rational entries of size n*)
randomHermitianMatrix[n_,maxNumerator_:1000,maxDenominator_:1000]:=Module[{realPart,imagPart,matrix},
(*Generate the random rational real part matrix*)
realPart=Table[randomRational[maxNumerator,maxDenominator],{n},{n}];
(*Generate the random rational imaginary part matrix*)
imagPart=Table[randomRational[maxNumerator,maxDenominator],{n},{n}];
(*Create the random complex matrix*)
matrix=realPart+I imagPart;
(*Make the matrix Hermitian*)
(matrix+ConjugateTranspose[matrix])/2]

(*Function generating a random Hermitian matirx of unit trace*)
randomHermitianMatrixUnitTrace[n_,maxNumerator_:1000,maxDenominator_:1000]:=Module[{H},
H = randomHermitianMatrix[n,maxNumerator,maxDenominator];
H/Tr[H]]
(*2. Necessary early functions on polynomials*)
(*Leading Coefficient*)
leadingCoeff[poly_,var_:t]:=Coefficient[poly,var,Exponent[poly,var]]
(*Function to check if a point is a root of a polynomial*)
isRoot[p_,pt_,var_:t]:=(p/. var->pt)==0
(*Function returning GCD of 2 polynomials, found using Euclid's algorithm*)
polyGCD[p1_,p2_,var_:t]:=Module[{a,b,q,r},
a=p1;
b=p2;
While[b=!=0,
{q,r}=PolynomialQuotientRemainder[a,b,var];
a=b;
b=r;];
a]

(*Function returning remainders in Euclid's algorithm*)
euclidRemainders[p1_,p2_,var_:t]:=Module[{a,b,q,r,remainders},
(*Initialize with the first polynomial*)
a=p1;
b=p2;
remainders={a};
While[b=!=0,
{q,r}=PolynomialQuotientRemainder[a,b,var];
(*Append the current divisor*)
AppendTo[remainders,b];
a=b;
b=r;];
remainders]

(*Function returning a sturm sequence for a polynomial*)
sturmSequence[p_,var_:t]:=Module[{seq,q,r},
(*Start with the polynomial and its derivative*)
seq={p,D[p,var]};
While[Last[seq]=!=0,
{q,r}=PolynomialQuotientRemainder[seq[[-2]],seq[[-1]],var];
AppendTo[seq,-r]; ];
(*Remove the last zero*)
Most[seq] ]

(*Find the number of zeros of a polynomial on the interval (a,b) by applying Sturm theorem*)
countRealRootsInInterval[p_,a_,b_,var_:t]:=Module[{sturmSeq,signChanges},
sturmSeq=sturmSequence[p,var];
(*Function counting sign changes in the sequence*)
signChangesAt[pt_]:=Count[Differences[Sign[sturmSeq/. var->pt]],_?(#!=0&)];
signChangesAt[a]-signChangesAt[b]]

(*Function returning p tilde from p - Polynomial with single roots*)

reduceRootMultiplicities[p_,var_:t]:=Module[{gcd},
gcd = polyGCD[p,D[p,var],var];
{PolynomialQuotient[p,gcd,var],gcd}];

(*Function returning the sequence d from proposition 4.4, for a given polynomial*)
dSequence[p_,a_,b_,var_:t]:=Module[{d,f,g,di},
d ={};
{f,g} = reduceRootMultiplicities[p,var];

di = countRealRootsInInterval[f,a,b,var];
AppendTo[d,di];
While[Last[d]=!=0,
{f,g} = reduceRootMultiplicities[g,var];
di = countRealRootsInInterval[f,a,b,var];
AppendTo[d,di];];
d] 
(*Function Returning Reduced Polynomials as well as sequence d*)
dSequenceWithPolyList[p_,a_,b_,var_:t]:=Module[{polyList,d,f,g,di},
d = {};
polyList ={};
{f,g} = reduceRootMultiplicities[p,var];

di = countRealRootsInInterval[f,a,b,var];
AppendTo[d,di];
AppendTo[polyList,f];
While[Last[d]=!=0,
{f,g} = reduceRootMultiplicities[g,var];
di = countRealRootsInInterval[f,a,b,var];
AppendTo[polyList,f];
AppendTo[d,di]];
{polyList,d}] 

(*Construct Sigma Polynomial from odd multiplicity roots of polynomial p*)
sigmaPolynomial[p_,a_,b_,var_:t]:=Module[{polyList,throwaway,sigma},
sigma = 1;
{polyList,throwaway} = dSequenceWithPolyList[p,a,b,var];
For[i=0,2i+2<=Length[polyList],i++,
sigma *=PolynomialQuotient[polyList[[2i+1]],polyList[[2i+2]],var]];
sigma]

(*sigmapolynomiall - polynomial with all roots??? This is probably the same as f tilde*)
sigmaPolynomialAll[p_,a_,b_,var_:t]:=Module[{polyList,Throwaway,sigma},
sigma = 1;
{polyList,Throwaway} = dSequenceWithPolyList[p,a,b,var];
For[i=1,i<Length[polyList],i++,
sigma *=PolynomialQuotient[polyList[[i]],polyList[[i+1]],var]];
sigma]

(*3. Functions on lists*)

(*Function to find positions where the k-th element is not equal to the (k-1)-th element*)

findPositionDifferences[list_]:=Module[{positions},
positions={};
Do[If[list[[k]]!=list[[k-1]],AppendTo[positions,k]],{k,2,Length[list]}];
positions]

(* Function to check if there is an even number in the list. Returns T/F*)
containsEvenNumberQ[list_] := Module[{evenFound},
  evenFound = False;
  Do[
    If[EvenQ[element],
      evenFound = True;
      Break[];
    ],
    {element, list}
  ];
  evenFound
]

(*4. Nonnegativity check*)
(*Function to check nonnegaivity of an arbitrary polynomial p*)
polynomialNonnegativityQ[p_,var_:t]:=Module[{deg,leadCof,diff},
If[p==0,Return[True]];
deg = Exponent[p,var];
leadCof = leadingCoeff[p,var];
diff = findPositionDifferences[dSequence[p,-100^15,100^15,var]];
(*Positive leading coefficient even degree, no odd multiplicity roots*)
And[EvenQ[deg],leadCof>0,Not[containsEvenNumberQ[diff]]]]

(*Recursive function to generate the mesh of points - Algorithm 1*)
genMesh[g1_,g2_,a_,b_,var_:t]:=Module[{rootsG1,rootsG2,mid,leftMesh,rightMesh,reducedG1,reducedG2,throwaway,offset},
{reducedG1,throwaway} = reduceRootMultiplicities[g1,var];
{reducedG2,throwaway} = reduceRootMultiplicities[g2,var];
rootsG1=countRealRootsInInterval[reducedG1,a,b,var];
rootsG2=countRealRootsInInterval[reducedG2,a,b,var];
(*If both polynomials have at most one root in the interval,return the endpoints*)
If[rootsG1<=1&&rootsG2<=1,Return[{a,b}]];
(*Otherwise,bisect the interval*)
mid=(a+b)/2;

While[Or[isRoot[g1,mid,var],isRoot[g2,mid,var]],
offset = (mid+b)/2;
mid+=offset];
(*Recursively generate meshes for the left and right subintervals*)
leftMesh=genMesh[g1,g2,a,mid,var];
rightMesh=genMesh[g1,g2,mid,b,var];
(*Combine the meshes,removing the duplicate midpoint*)
Return[Join[Most[leftMesh],rightMesh]]]



(*Function testing polynomial precedence Algorithm 2*)
polynomialPrecedence[g1_,g2_,a_,b_, var_:t]:=Module[{s1,s2,mid},
mid = (a+b)/2;
s1 = (g1/.var->mid)*(g1/.var->a);
s2 = (g2/.var->mid)*(g2/.var->a);
If[And[s1<=0,s2>0],Return[True]];
If[And[s1>0,s2<=0],Return[False]];
If[And[s1>0,s2>0],Return[polynomialPrecedence[g1,g2,mid,b,var]]];
polynomialPrecedence[g1,g2,a,mid,var]]

(*Function testing if two polynomials have common roots on an interval returns a number*)
commonRootsQ[g1_,g2_,a_,b_,var_:t]:=Module[{sigma1,sigma2},
sigma1 = sigmaPolynomialAll[g1,a,b,var];
sigma2 = sigmaPolynomialAll[g2,a,b,var];
countRealRootsInInterval[polyGCD[sigma1,sigma2,var],a,b,var]]

(*Function testing if two polynomials are nonnegative on a single interval (t_i,t_{i+1})*)
singleIntervalTest[g1_,g2_,a_,b_,var_:t]:=Module[{g1a,g2a,g1b,g2b},
{g1a,g2a,g1b,g2b} = {g1/.var->a,g2/.var->a,g1/.var->b,g2/.var->b};
(*Cases 10-16*)
If[Or[And[g1a<0,g2a<0],And[g1b<0,g2b<0]],Return[False]];
(*Cases 1-7*)
If[Or[And[g1a>0,g1b>0],And[g2a>0,g2b>0]],Return[True]];
If[commonRootsQ[g1,g2,a,b,var]>0,Return[True]];
If[g1a>0,Return[Not[polynomialPrecedence[g1,g2,a,b,var]]]];
If[g1a<0,Return[polynomialPrecedence[g1,g2,a,b,var]]]
]


twoPolyForFullDomain[g1_,g2_,var_:t]:=Module[{},
	If[And[leadingCoeff[g1]<0,leadingCoeff[g2]<0],Return[False]];
	If[And[Coefficient[g1,var,0]<0,Coefficient[g2,var,0]<0],Return[False]];
	Return[True]]
	
(*Function to check nonnegativity of two polynomials on an interval (a,b)*)
twoPolyNonnegativityQ[g1_,g2_,a_,b_,var_:t]:=Module[{intervalMesh,i,test},
If[Or[polynomialNonnegativityQ[g1],polynomialNonnegativityQ[g2]],Return[True]];
intervalMesh = genMesh[g1,g2,a,b,var];
i= 1;
test = True;
While[And[test,i+1<=Length[intervalMesh]],
test = singleIntervalTest[g1,g2,intervalMesh[[i]],intervalMesh[[i+1]],var];
i+=1];
Return[test]
]
(*5. Apllication to a 4x4 matrix*)
(*Function to construct c coefficients from equation (5.14)*)
cCoefficients[m_]:=Module[{c1,c2,c3,c4,c5,c6},
c1 = m[[2,2]]*m[[4,4]]-Conjugate[m[[2,4]]]*m[[2,4]];
c2 = m[[4,4]]m[[1,2]]+m[[2,2]]m[[3,4]]-m[[2,4]]*Conjugate[m[[2,3]]]-Conjugate[m[[2,4]]]m[[1,4]];
c3 = m[[1,2]]m[[3,4]]-m[[1,4]]Conjugate[m[[2,3]]];
c4 = m[[1,2]]Conjugate[m[[3,4]]]-m[[2,4]]Conjugate[m[[1,3]]]+Conjugate[m[[1,2]]]m[[3,4]]-Conjugate[m[[2,4]]]m[[1,3]]+Conjugate[m[[1,4]]]m[[1,4]]+Conjugate[m[[2,3]]]m[[2,3]]+m[[1,1]]m[[4,4]]+m[[2,2]]m[[3,3]];
c5 = m[[1,1]]m[[3,4]]+m[[3,3]]m[[1,2]]-Conjugate[m[[1,3]]]*m[[1,4]]-m[[1,3]]*Conjugate[m[[2,3]]];
c6 = m[[1,1]]m[[3,3]]-Conjugate[m[[1,3]]]m[[1,3]];
Return[{c1,c2,c3,c4,c5,c6}]]

(*Some Expressions*)
\[Chi][t_,c_,d_]:=(2*Re[c]+d)t^4+8Im[c]t^3+2(d-6Re[c])t^2-8Im[c]t+2Re[c]+d;
\[CapitalLambda][t_,b_]:=Re[b]t^2+2Im[b]t-Re[b];

(*Function to generate fdelta polynomial from c coefficients*)
genfdeltaPoly[{a1_,a2_,a3_,a4_,a5_,a6_}]:=Module[{expression},
expression =16 a6^2 (a1 a4^4 a6-8 a1^2 a4^2 a6^2+16 a1^3 a6^3+8 a1 a4^4 a6 t^2-64 a1^2 a4^2 a6^2 t^2+128 a1^3 a6^3 t^2+28 a1 a4^4 a6 t^4-224 a1^2 a4^2 a6^2 t^4+448 a1^3 a6^3 t^4+56 a1 a4^4 a6 t^6-448 a1^2 a4^2 a6^2 t^6+896 a1^3 a6^3 t^6+70 a1 a4^4 a6 t^8-560 a1^2 a4^2 a6^2 t^8+1120 a1^3 a6^3 t^8+56 a1 a4^4 a6 t^10-448 a1^2 a4^2 a6^2 t^10+896 a1^3 a6^3 t^10+28 a1 a4^4 a6 t^12-224 a1^2 a4^2 a6^2 t^12+448 a1^3 a6^3 t^12+8 a1 a4^4 a6 t^14-64 a1^2 a4^2 a6^2 t^14+128 a1^3 a6^3 t^14+a1 a4^4 a6 t^16-8 a1^2 a4^2 a6^2 t^16+16 a1^3 a6^3 t^16-432 a6^2 (t+t^3)^4 Im[a2]^4+4096 a1 a6 t^4 (-1+t^2)^4 Im[a3]^4-4 a1 a4^3 t^2 Im[a5]^2+144 a1^2 a4 a6 t^2 Im[a5]^2-24 a1 a4^3 t^4 Im[a5]^2+864 a1^2 a4 a6 t^4 Im[a5]^2-60 a1 a4^3 t^6 Im[a5]^2+2160 a1^2 a4 a6 t^6 Im[a5]^2-80 a1 a4^3 t^8 Im[a5]^2+2880 a1^2 a4 a6 t^8 Im[a5]^2-60 a1 a4^3 t^10 Im[a5]^2+2160 a1^2 a4 a6 t^10 Im[a5]^2-24 a1 a4^3 t^12 Im[a5]^2+864 a1^2 a4 a6 t^12 Im[a5]^2-4 a1 a4^3 t^14 Im[a5]^2+144 a1^2 a4 a6 t^14 Im[a5]^2-432 a1^2 t^4 Im[a5]^4-1728 a1^2 t^6 Im[a5]^4-2592 a1^2 t^8 Im[a5]^4-1728 a1^2 t^10 Im[a5]^4-432 a1^2 t^12 Im[a5]^4+40 a1 a4^2 a6 t Im[a5] Re[a2]+96 a1^2 a6^2 t Im[a5] Re[a2]+200 a1 a4^2 a6 t^3 Im[a5] Re[a2]+480 a1^2 a6^2 t^3 Im[a5] Re[a2]+360 a1 a4^2 a6 t^5 Im[a5] Re[a2]+864 a1^2 a6^2 t^5 Im[a5] Re[a2]+200 a1 a4^2 a6 t^7 Im[a5] Re[a2]+480 a1^2 a6^2 t^7 Im[a5] Re[a2]-200 a1 a4^2 a6 t^9 Im[a5] Re[a2]-480 a1^2 a6^2 t^9 Im[a5] Re[a2]-360 a1 a4^2 a6 t^11 Im[a5] Re[a2]-864 a1^2 a6^2 t^11 Im[a5] Re[a2]-200 a1 a4^2 a6 t^13 Im[a5] Re[a2]-480 a1^2 a6^2 t^13 Im[a5] Re[a2]-40 a1 a4^2 a6 t^15 Im[a5] Re[a2]-96 a1^2 a6^2 t^15 Im[a5] Re[a2]-144 a1 a4 t^3 Im[a5]^3 Re[a2]-432 a1 a4 t^5 Im[a5]^3 Re[a2]-288 a1 a4 t^7 Im[a5]^3 Re[a2]+288 a1 a4 t^9 Im[a5]^3 Re[a2]+432 a1 a4 t^11 Im[a5]^3 Re[a2]+144 a1 a4 t^13 Im[a5]^3 Re[a2]-a4^3 a6 Re[a2]^2+36 a1 a4 a6^2 Re[a2]^2-4 a4^3 a6 t^2 Re[a2]^2+144 a1 a4 a6^2 t^2 Re[a2]^2-4 a4^3 a6 t^4 Re[a2]^2+144 a1 a4 a6^2 t^4 Re[a2]^2+4 a4^3 a6 t^6 Re[a2]^2-144 a1 a4 a6^2 t^6 Re[a2]^2+10 a4^3 a6 t^8 Re[a2]^2-360 a1 a4 a6^2 t^8 Re[a2]^2+4 a4^3 a6 t^10 Re[a2]^2-144 a1 a4 a6^2 t^10 Re[a2]^2-4 a4^3 a6 t^12 Re[a2]^2+144 a1 a4 a6^2 t^12 Re[a2]^2-4 a4^3 a6 t^14 Re[a2]^2+144 a1 a4 a6^2 t^14 Re[a2]^2-a4^3 a6 t^16 Re[a2]^2+36 a1 a4 a6^2 t^16 Re[a2]^2+4 a4^2 t^2 Im[a5]^2 Re[a2]^2-24 a1 a6 t^2 Im[a5]^2 Re[a2]^2+8 a4^2 t^4 Im[a5]^2 Re[a2]^2-48 a1 a6 t^4 Im[a5]^2 Re[a2]^2-4 a4^2 t^6 Im[a5]^2 Re[a2]^2+24 a1 a6 t^6 Im[a5]^2 Re[a2]^2-16 a4^2 t^8 Im[a5]^2 Re[a2]^2+96 a1 a6 t^8 Im[a5]^2 Re[a2]^2-4 a4^2 t^10 Im[a5]^2 Re[a2]^2+24 a1 a6 t^10 Im[a5]^2 Re[a2]^2+8 a4^2 t^12 Im[a5]^2 Re[a2]^2-48 a1 a6 t^12 Im[a5]^2 Re[a2]^2+4 a4^2 t^14 Im[a5]^2 Re[a2]^2-24 a1 a6 t^14 Im[a5]^2 Re[a2]^2-36 a4 a6 t Im[a5] Re[a2]^3-36 a4 a6 t^3 Im[a5] Re[a2]^3+108 a4 a6 t^5 Im[a5] Re[a2]^3+108 a4 a6 t^7 Im[a5] Re[a2]^3-108 a4 a6 t^9 Im[a5] Re[a2]^3-108 a4 a6 t^11 Im[a5] Re[a2]^3+36 a4 a6 t^13 Im[a5] Re[a2]^3+36 a4 a6 t^15 Im[a5] Re[a2]^3+128 t^3 Im[a5]^3 Re[a2]^3-128 t^5 Im[a5]^3 Re[a2]^3-256 t^7 Im[a5]^3 Re[a2]^3+256 t^9 Im[a5]^3 Re[a2]^3+128 t^11 Im[a5]^3 Re[a2]^3-128 t^13 Im[a5]^3 Re[a2]^3-27 a6^2 Re[a2]^4+108 a6^2 t^4 Re[a2]^4-162 a6^2 t^8 Re[a2]^4+108 a6^2 t^12 Re[a2]^4-27 a6^2 t^16 Re[a2]^4+8 a1 a4^3 a6 Re[a3]-32 a1^2 a4 a6^2 Re[a3]-160 a1 a4^3 a6 t^4 Re[a3]+640 a1^2 a4 a6^2 t^4 Re[a3]-512 a1 a4^3 a6 t^6 Re[a3]+2048 a1^2 a4 a6^2 t^6 Re[a3]-720 a1 a4^3 a6 t^8 Re[a3]+2880 a1^2 a4 a6^2 t^8 Re[a3]-512 a1 a4^3 a6 t^10 Re[a3]+2048 a1^2 a4 a6^2 t^10 Re[a3]-160 a1 a4^3 a6 t^12 Re[a3]+640 a1^2 a4 a6^2 t^12 Re[a3]+8 a1 a4^3 a6 t^16 Re[a3]-32 a1^2 a4 a6^2 t^16 Re[a3]-24 a1 a4^2 t^2 Im[a5]^2 Re[a3]+288 a1^2 a6 t^2 Im[a5]^2 Re[a3]+48 a1 a4^2 t^4 Im[a5]^2 Re[a3]-576 a1^2 a6 t^4 Im[a5]^2 Re[a3]+408 a1 a4^2 t^6 Im[a5]^2 Re[a3]-4896 a1^2 a6 t^6 Im[a5]^2 Re[a3]+672 a1 a4^2 t^8 Im[a5]^2 Re[a3]-8064 a1^2 a6 t^8 Im[a5]^2 Re[a3]+408 a1 a4^2 t^10 Im[a5]^2 Re[a3]-4896 a1^2 a6 t^10 Im[a5]^2 Re[a3]+48 a1 a4^2 t^12 Im[a5]^2 Re[a3]-576 a1^2 a6 t^12 Im[a5]^2 Re[a3]-24 a1 a4^2 t^14 Im[a5]^2 Re[a3]+288 a1^2 a6 t^14 Im[a5]^2 Re[a3]+160 a1 a4 a6 t Im[a5] Re[a2] Re[a3]-480 a1 a4 a6 t^3 Im[a5] Re[a2] Re[a3]-2400 a1 a4 a6 t^5 Im[a5] Re[a2] Re[a3]-1760 a1 a4 a6 t^7 Im[a5] Re[a2] Re[a3]+1760 a1 a4 a6 t^9 Im[a5] Re[a2] Re[a3]+2400 a1 a4 a6 t^11 Im[a5] Re[a2] Re[a3]+480 a1 a4 a6 t^13 Im[a5] Re[a2] Re[a3]-160 a1 a4 a6 t^15 Im[a5] Re[a2] Re[a3]-288 a1 t^3 Im[a5]^3 Re[a2] Re[a3]+1440 a1 t^5 Im[a5]^3 Re[a2] Re[a3]+1728 a1 t^7 Im[a5]^3 Re[a2] Re[a3]-1728 a1 t^9 Im[a5]^3 Re[a2] Re[a3]-1440 a1 t^11 Im[a5]^3 Re[a2] Re[a3]+288 a1 t^13 Im[a5]^3 Re[a2] Re[a3]-6 a4^2 a6 Re[a2]^2 Re[a3]+72 a1 a6^2 Re[a2]^2 Re[a3]+24 a4^2 a6 t^2 Re[a2]^2 Re[a3]-288 a1 a6^2 t^2 Re[a2]^2 Re[a3]+72 a4^2 a6 t^4 Re[a2]^2 Re[a3]-864 a1 a6^2 t^4 Re[a2]^2 Re[a3]-24 a4^2 a6 t^6 Re[a2]^2 Re[a3]+288 a1 a6^2 t^6 Re[a2]^2 Re[a3]-132 a4^2 a6 t^8 Re[a2]^2 Re[a3]+1584 a1 a6^2 t^8 Re[a2]^2 Re[a3]-24 a4^2 a6 t^10 Re[a2]^2 Re[a3]+288 a1 a6^2 t^10 Re[a2]^2 Re[a3]+72 a4^2 a6 t^12 Re[a2]^2 Re[a3]-864 a1 a6^2 t^12 Re[a2]^2 Re[a3]+24 a4^2 a6 t^14 Re[a2]^2 Re[a3]-288 a1 a6^2 t^14 Re[a2]^2 Re[a3]-6 a4^2 a6 t^16 Re[a2]^2 Re[a3]+72 a1 a6^2 t^16 Re[a2]^2 Re[a3]+16 a4 t^2 Im[a5]^2 Re[a2]^2 Re[a3]-96 a4 t^4 Im[a5]^2 Re[a2]^2 Re[a3]-16 a4 t^6 Im[a5]^2 Re[a2]^2 Re[a3]+192 a4 t^8 Im[a5]^2 Re[a2]^2 Re[a3]-16 a4 t^10 Im[a5]^2 Re[a2]^2 Re[a3]-96 a4 t^12 Im[a5]^2 Re[a2]^2 Re[a3]+16 a4 t^14 Im[a5]^2 Re[a2]^2 Re[a3]-72 a6 t Im[a5] Re[a2]^3 Re[a3]+504 a6 t^3 Im[a5] Re[a2]^3 Re[a3]-360 a6 t^5 Im[a5] Re[a2]^3 Re[a3]-936 a6 t^7 Im[a5] Re[a2]^3 Re[a3]+936 a6 t^9 Im[a5] Re[a2]^3 Re[a3]+360 a6 t^11 Im[a5] Re[a2]^3 Re[a3]-504 a6 t^13 Im[a5] Re[a2]^3 Re[a3]+72 a6 t^15 Im[a5] Re[a2]^3 Re[a3]+24 a1 a4^2 a6 Re[a3]^2-32 a1^2 a6^2 Re[a3]^2-192 a1 a4^2 a6 t^2 Re[a3]^2+256 a1^2 a6^2 t^2 Re[a3]^2-96 a1 a4^2 a6 t^4 Re[a3]^2+128 a1^2 a6^2 t^4 Re[a3]^2+1728 a1 a4^2 a6 t^6 Re[a3]^2-2304 a1^2 a6^2 t^6 Re[a3]^2+3216 a1 a4^2 a6 t^8 Re[a3]^2-4288 a1^2 a6^2 t^8 Re[a3]^2+1728 a1 a4^2 a6 t^10 Re[a3]^2-2304 a1^2 a6^2 t^10 Re[a3]^2-96 a1 a4^2 a6 t^12 Re[a3]^2+128 a1^2 a6^2 t^12 Re[a3]^2-192 a1 a4^2 a6 t^14 Re[a3]^2+256 a1^2 a6^2 t^14 Re[a3]^2+24 a1 a4^2 a6 t^16 Re[a3]^2-32 a1^2 a6^2 t^16 Re[a3]^2-48 a1 a4 t^2 Im[a5]^2 Re[a3]^2+480 a1 a4 t^4 Im[a5]^2 Re[a3]^2-720 a1 a4 t^6 Im[a5]^2 Re[a3]^2-2496 a1 a4 t^8 Im[a5]^2 Re[a3]^2-720 a1 a4 t^10 Im[a5]^2 Re[a3]^2+480 a1 a4 t^12 Im[a5]^2 Re[a3]^2-48 a1 a4 t^14 Im[a5]^2 Re[a3]^2+160 a1 a6 t Im[a5] Re[a2] Re[a3]^2-1760 a1 a6 t^3 Im[a5] Re[a2] Re[a3]^2+4000 a1 a6 t^5 Im[a5] Re[a2] Re[a3]^2+5920 a1 a6 t^7 Im[a5] Re[a2] Re[a3]^2-5920 a1 a6 t^9 Im[a5] Re[a2] Re[a3]^2-4000 a1 a6 t^11 Im[a5] Re[a2] Re[a3]^2+1760 a1 a6 t^13 Im[a5] Re[a2] Re[a3]^2-160 a1 a6 t^15 Im[a5] Re[a2] Re[a3]^2-12 a4 a6 Re[a2]^2 Re[a3]^2+144 a4 a6 t^2 Re[a2]^2 Re[a3]^2-432 a4 a6 t^4 Re[a2]^2 Re[a3]^2-144 a4 a6 t^6 Re[a2]^2 Re[a3]^2+888 a4 a6 t^8 Re[a2]^2 Re[a3]^2-144 a4 a6 t^10 Re[a2]^2 Re[a3]^2-432 a4 a6 t^12 Re[a2]^2 Re[a3]^2+144 a4 a6 t^14 Re[a2]^2 Re[a3]^2-12 a4 a6 t^16 Re[a2]^2 Re[a3]^2+16 t^2 Im[a5]^2 Re[a2]^2 Re[a3]^2-224 t^4 Im[a5]^2 Re[a2]^2 Re[a3]^2+1008 t^6 Im[a5]^2 Re[a2]^2 Re[a3]^2-1600 t^8 Im[a5]^2 Re[a2]^2 Re[a3]^2+1008 t^10 Im[a5]^2 Re[a2]^2 Re[a3]^2-224 t^12 Im[a5]^2 Re[a2]^2 Re[a3]^2+16 t^14 Im[a5]^2 Re[a2]^2 Re[a3]^2+32 a1 a4 a6 Re[a3]^3-512 a1 a4 a6 t^2 Re[a3]^3+2432 a1 a4 a6 t^4 Re[a3]^3-1536 a1 a4 a6 t^6 Re[a3]^3-9024 a1 a4 a6 t^8 Re[a3]^3-1536 a1 a4 a6 t^10 Re[a3]^3+2432 a1 a4 a6 t^12 Re[a3]^3-512 a1 a4 a6 t^14 Re[a3]^3+32 a1 a4 a6 t^16 Re[a3]^3-32 a1 t^2 Im[a5]^2 Re[a3]^3+576 a1 t^4 Im[a5]^2 Re[a3]^3-3552 a1 t^6 Im[a5]^2 Re[a3]^3+8064 a1 t^8 Im[a5]^2 Re[a3]^3-3552 a1 t^10 Im[a5]^2 Re[a3]^3+576 a1 t^12 Im[a5]^2 Re[a3]^3-32 a1 t^14 Im[a5]^2 Re[a3]^3-8 a6 Re[a2]^2 Re[a3]^3+160 a6 t^2 Re[a2]^2 Re[a3]^3-1184 a6 t^4 Re[a2]^2 Re[a3]^3+3936 a6 t^6 Re[a2]^2 Re[a3]^3-5808 a6 t^8 Re[a2]^2 Re[a3]^3+3936 a6 t^10 Re[a2]^2 Re[a3]^3-1184 a6 t^12 Re[a2]^2 Re[a3]^3+160 a6 t^14 Re[a2]^2 Re[a3]^3-8 a6 t^16 Re[a2]^2 Re[a3]^3+16 a1 a6 Re[a3]^4-384 a1 a6 t^2 Re[a3]^4+3520 a1 a6 t^4 Re[a3]^4-14976 a1 a6 t^6 Re[a3]^4+27744 a1 a6 t^8 Re[a3]^4-14976 a1 a6 t^10 Re[a3]^4+3520 a1 a6 t^12 Re[a3]^4-384 a1 a6 t^14 Re[a3]^4+16 a1 a6 t^16 Re[a3]^4+4 a1 a4^3 t Im[a5] Re[a5]-144 a1^2 a4 a6 t Im[a5] Re[a5]+20 a1 a4^3 t^3 Im[a5] Re[a5]-720 a1^2 a4 a6 t^3 Im[a5] Re[a5]+36 a1 a4^3 t^5 Im[a5] Re[a5]-1296 a1^2 a4 a6 t^5 Im[a5] Re[a5]+20 a1 a4^3 t^7 Im[a5] Re[a5]-720 a1^2 a4 a6 t^7 Im[a5] Re[a5]-20 a1 a4^3 t^9 Im[a5] Re[a5]+720 a1^2 a4 a6 t^9 Im[a5] Re[a5]-36 a1 a4^3 t^11 Im[a5] Re[a5]+1296 a1^2 a4 a6 t^11 Im[a5] Re[a5]-20 a1 a4^3 t^13 Im[a5] Re[a5]+720 a1^2 a4 a6 t^13 Im[a5] Re[a5]-4 a1 a4^3 t^15 Im[a5] Re[a5]+144 a1^2 a4 a6 t^15 Im[a5] Re[a5]+864 a1^2 t^3 Im[a5]^3 Re[a5]+2592 a1^2 t^5 Im[a5]^3 Re[a5]+1728 a1^2 t^7 Im[a5]^3 Re[a5]-1728 a1^2 t^9 Im[a5]^3 Re[a5]-2592 a1^2 t^11 Im[a5]^3 Re[a5]-864 a1^2 t^13 Im[a5]^3 Re[a5]-20 a1 a4^2 a6 Re[a2] Re[a5]-48 a1^2 a6^2 Re[a2] Re[a5]-80 a1 a4^2 a6 t^2 Re[a2] Re[a5]-192 a1^2 a6^2 t^2 Re[a2] Re[a5]-80 a1 a4^2 a6 t^4 Re[a2] Re[a5]-192 a1^2 a6^2 t^4 Re[a2] Re[a5]+80 a1 a4^2 a6 t^6 Re[a2] Re[a5]+192 a1^2 a6^2 t^6 Re[a2] Re[a5]+200 a1 a4^2 a6 t^8 Re[a2] Re[a5]+480 a1^2 a6^2 t^8 Re[a2] Re[a5]+80 a1 a4^2 a6 t^10 Re[a2] Re[a5]+192 a1^2 a6^2 t^10 Re[a2] Re[a5]-80 a1 a4^2 a6 t^12 Re[a2] Re[a5]-192 a1^2 a6^2 t^12 Re[a2] Re[a5]-80 a1 a4^2 a6 t^14 Re[a2] Re[a5]-192 a1^2 a6^2 t^14 Re[a2] Re[a5]-20 a1 a4^2 a6 t^16 Re[a2] Re[a5]-48 a1^2 a6^2 t^16 Re[a2] Re[a5]+216 a1 a4 t^2 Im[a5]^2 Re[a2] Re[a5]+432 a1 a4 t^4 Im[a5]^2 Re[a2] Re[a5]-216 a1 a4 t^6 Im[a5]^2 Re[a2] Re[a5]-864 a1 a4 t^8 Im[a5]^2 Re[a2] Re[a5]-216 a1 a4 t^10 Im[a5]^2 Re[a2] Re[a5]+432 a1 a4 t^12 Im[a5]^2 Re[a2] Re[a5]+216 a1 a4 t^14 Im[a5]^2 Re[a2] Re[a5]-4 a4^2 t Im[a5] Re[a2]^2 Re[a5]+24 a1 a6 t Im[a5] Re[a2]^2 Re[a5]-4 a4^2 t^3 Im[a5] Re[a2]^2 Re[a5]+24 a1 a6 t^3 Im[a5] Re[a2]^2 Re[a5]+12 a4^2 t^5 Im[a5] Re[a2]^2 Re[a5]-72 a1 a6 t^5 Im[a5] Re[a2]^2 Re[a5]+12 a4^2 t^7 Im[a5] Re[a2]^2 Re[a5]-72 a1 a6 t^7 Im[a5] Re[a2]^2 Re[a5]-12 a4^2 t^9 Im[a5] Re[a2]^2 Re[a5]+72 a1 a6 t^9 Im[a5] Re[a2]^2 Re[a5]-12 a4^2 t^11 Im[a5] Re[a2]^2 Re[a5]+72 a1 a6 t^11 Im[a5] Re[a2]^2 Re[a5]+4 a4^2 t^13 Im[a5] Re[a2]^2 Re[a5]-24 a1 a6 t^13 Im[a5] Re[a2]^2 Re[a5]+4 a4^2 t^15 Im[a5] Re[a2]^2 Re[a5]-24 a1 a6 t^15 Im[a5] Re[a2]^2 Re[a5]+18 a4 a6 Re[a2]^3 Re[a5]-72 a4 a6 t^4 Re[a2]^3 Re[a5]+108 a4 a6 t^8 Re[a2]^3 Re[a5]-72 a4 a6 t^12 Re[a2]^3 Re[a5]+18 a4 a6 t^16 Re[a2]^3 Re[a5]-192 t^2 Im[a5]^2 Re[a2]^3 Re[a5]+384 t^4 Im[a5]^2 Re[a2]^3 Re[a5]+192 t^6 Im[a5]^2 Re[a2]^3 Re[a5]-768 t^8 Im[a5]^2 Re[a2]^3 Re[a5]+192 t^10 Im[a5]^2 Re[a2]^3 Re[a5]+384 t^12 Im[a5]^2 Re[a2]^3 Re[a5]-192 t^14 Im[a5]^2 Re[a2]^3 Re[a5]+24 a1 a4^2 t Im[a5] Re[a3] Re[a5]-288 a1^2 a6 t Im[a5] Re[a3] Re[a5]-72 a1 a4^2 t^3 Im[a5] Re[a3] Re[a5]+864 a1^2 a6 t^3 Im[a5] Re[a3] Re[a5]-360 a1 a4^2 t^5 Im[a5] Re[a3] Re[a5]+4320 a1^2 a6 t^5 Im[a5] Re[a3] Re[a5]-264 a1 a4^2 t^7 Im[a5] Re[a3] Re[a5]+3168 a1^2 a6 t^7 Im[a5] Re[a3] Re[a5]+264 a1 a4^2 t^9 Im[a5] Re[a3] Re[a5]-3168 a1^2 a6 t^9 Im[a5] Re[a3] Re[a5]+360 a1 a4^2 t^11 Im[a5] Re[a3] Re[a5]-4320 a1^2 a6 t^11 Im[a5] Re[a3] Re[a5]+72 a1 a4^2 t^13 Im[a5] Re[a3] Re[a5]-864 a1^2 a6 t^13 Im[a5] Re[a3] Re[a5]-24 a1 a4^2 t^15 Im[a5] Re[a3] Re[a5]+288 a1^2 a6 t^15 Im[a5] Re[a3] Re[a5]-80 a1 a4 a6 Re[a2] Re[a3] Re[a5]+320 a1 a4 a6 t^2 Re[a2] Re[a3] Re[a5]+960 a1 a4 a6 t^4 Re[a2] Re[a3] Re[a5]-320 a1 a4 a6 t^6 Re[a2] Re[a3] Re[a5]-1760 a1 a4 a6 t^8 Re[a2] Re[a3] Re[a5]-320 a1 a4 a6 t^10 Re[a2] Re[a3] Re[a5]+960 a1 a4 a6 t^12 Re[a2] Re[a3] Re[a5]+320 a1 a4 a6 t^14 Re[a2] Re[a3] Re[a5]-80 a1 a4 a6 t^16 Re[a2] Re[a3] Re[a5]+432 a1 t^2 Im[a5]^2 Re[a2] Re[a3] Re[a5]-2592 a1 t^4 Im[a5]^2 Re[a2] Re[a3] Re[a5]-432 a1 t^6 Im[a5]^2 Re[a2] Re[a3] Re[a5]+5184 a1 t^8 Im[a5]^2 Re[a2] Re[a3] Re[a5]-432 a1 t^10 Im[a5]^2 Re[a2] Re[a3] Re[a5]-2592 a1 t^12 Im[a5]^2 Re[a2] Re[a3] Re[a5]+432 a1 t^14 Im[a5]^2 Re[a2] Re[a3] Re[a5]-16 a4 t Im[a5] Re[a2]^2 Re[a3] Re[a5]+112 a4 t^3 Im[a5] Re[a2]^2 Re[a3] Re[a5]-80 a4 t^5 Im[a5] Re[a2]^2 Re[a3] Re[a5]-208 a4 t^7 Im[a5] Re[a2]^2 Re[a3] Re[a5]+208 a4 t^9 Im[a5] Re[a2]^2 Re[a3] Re[a5]+80 a4 t^11 Im[a5] Re[a2]^2 Re[a3] Re[a5]-112 a4 t^13 Im[a5] Re[a2]^2 Re[a3] Re[a5]+16 a4 t^15 Im[a5] Re[a2]^2 Re[a3] Re[a5]+36 a6 Re[a2]^3 Re[a3] Re[a5]-288 a6 t^2 Re[a2]^3 Re[a3] Re[a5]+432 a6 t^4 Re[a2]^3 Re[a3] Re[a5]+288 a6 t^6 Re[a2]^3 Re[a3] Re[a5]-936 a6 t^8 Re[a2]^3 Re[a3] Re[a5]+288 a6 t^10 Re[a2]^3 Re[a3] Re[a5]+432 a6 t^12 Re[a2]^3 Re[a3] Re[a5]-288 a6 t^14 Re[a2]^3 Re[a3] Re[a5]+36 a6 t^16 Re[a2]^3 Re[a3] Re[a5]+48 a1 a4 t Im[a5] Re[a3]^2 Re[a5]-528 a1 a4 t^3 Im[a5] Re[a3]^2 Re[a5]+1200 a1 a4 t^5 Im[a5] Re[a3]^2 Re[a5]+1776 a1 a4 t^7 Im[a5] Re[a3]^2 Re[a5]-1776 a1 a4 t^9 Im[a5] Re[a3]^2 Re[a5]-1200 a1 a4 t^11 Im[a5] Re[a3]^2 Re[a5]+528 a1 a4 t^13 Im[a5] Re[a3]^2 Re[a5]-48 a1 a4 t^15 Im[a5] Re[a3]^2 Re[a5]-80 a1 a6 Re[a2] Re[a3]^2 Re[a5]+960 a1 a6 t^2 Re[a2] Re[a3]^2 Re[a5]-2880 a1 a6 t^4 Re[a2] Re[a3]^2 Re[a5]-960 a1 a6 t^6 Re[a2] Re[a3]^2 Re[a5]+5920 a1 a6 t^8 Re[a2] Re[a3]^2 Re[a5]-960 a1 a6 t^10 Re[a2] Re[a3]^2 Re[a5]-2880 a1 a6 t^12 Re[a2] Re[a3]^2 Re[a5]+960 a1 a6 t^14 Re[a2] Re[a3]^2 Re[a5]-80 a1 a6 t^16 Re[a2] Re[a3]^2 Re[a5]-16 t Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]+240 t^3 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]-1232 t^5 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]+2608 t^7 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]-2608 t^9 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]+1232 t^11 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]-240 t^13 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]+16 t^15 Im[a5] Re[a2]^2 Re[a3]^2 Re[a5]+32 a1 t Im[a5] Re[a3]^3 Re[a5]-608 a1 t^3 Im[a5] Re[a3]^3 Re[a5]+4128 a1 t^5 Im[a5] Re[a3]^3 Re[a5]-11616 a1 t^7 Im[a5] Re[a3]^3 Re[a5]+11616 a1 t^9 Im[a5] Re[a3]^3 Re[a5]-4128 a1 t^11 Im[a5] Re[a3]^3 Re[a5]+608 a1 t^13 Im[a5] Re[a3]^3 Re[a5]-32 a1 t^15 Im[a5] Re[a3]^3 Re[a5]-a1 a4^3 Re[a5]^2+36 a1^2 a4 a6 Re[a5]^2-4 a1 a4^3 t^2 Re[a5]^2+144 a1^2 a4 a6 t^2 Re[a5]^2-4 a1 a4^3 t^4 Re[a5]^2+144 a1^2 a4 a6 t^4 Re[a5]^2+4 a1 a4^3 t^6 Re[a5]^2-144 a1^2 a4 a6 t^6 Re[a5]^2+10 a1 a4^3 t^8 Re[a5]^2-360 a1^2 a4 a6 t^8 Re[a5]^2+4 a1 a4^3 t^10 Re[a5]^2-144 a1^2 a4 a6 t^10 Re[a5]^2-4 a1 a4^3 t^12 Re[a5]^2+144 a1^2 a4 a6 t^12 Re[a5]^2-4 a1 a4^3 t^14 Re[a5]^2+144 a1^2 a4 a6 t^14 Re[a5]^2-a1 a4^3 t^16 Re[a5]^2+36 a1^2 a4 a6 t^16 Re[a5]^2-648 a1^2 t^2 Im[a5]^2 Re[a5]^2-1296 a1^2 t^4 Im[a5]^2 Re[a5]^2+648 a1^2 t^6 Im[a5]^2 Re[a5]^2+2592 a1^2 t^8 Im[a5]^2 Re[a5]^2+648 a1^2 t^10 Im[a5]^2 Re[a5]^2-1296 a1^2 t^12 Im[a5]^2 Re[a5]^2-648 a1^2 t^14 Im[a5]^2 Re[a5]^2-108 a1 a4 t Im[a5] Re[a2] Re[a5]^2-108 a1 a4 t^3 Im[a5] Re[a2] Re[a5]^2+324 a1 a4 t^5 Im[a5] Re[a2] Re[a5]^2+324 a1 a4 t^7 Im[a5] Re[a2] Re[a5]^2-324 a1 a4 t^9 Im[a5] Re[a2] Re[a5]^2-324 a1 a4 t^11 Im[a5] Re[a2] Re[a5]^2+108 a1 a4 t^13 Im[a5] Re[a2] Re[a5]^2+108 a1 a4 t^15 Im[a5] Re[a2] Re[a5]^2+a4^2 Re[a2]^2 Re[a5]^2-6 a1 a6 Re[a2]^2 Re[a5]^2-4 a4^2 t^4 Re[a2]^2 Re[a5]^2+24 a1 a6 t^4 Re[a2]^2 Re[a5]^2+6 a4^2 t^8 Re[a2]^2 Re[a5]^2-36 a1 a6 t^8 Re[a2]^2 Re[a5]^2-4 a4^2 t^12 Re[a2]^2 Re[a5]^2+24 a1 a6 t^12 Re[a2]^2 Re[a5]^2+a4^2 t^16 Re[a2]^2 Re[a5]^2-6 a1 a6 t^16 Re[a2]^2 Re[a5]^2+96 t Im[a5] Re[a2]^3 Re[a5]^2-288 t^3 Im[a5] Re[a2]^3 Re[a5]^2+96 t^5 Im[a5] Re[a2]^3 Re[a5]^2+480 t^7 Im[a5] Re[a2]^3 Re[a5]^2-480 t^9 Im[a5] Re[a2]^3 Re[a5]^2-96 t^11 Im[a5] Re[a2]^3 Re[a5]^2+288 t^13 Im[a5] Re[a2]^3 Re[a5]^2-96 t^15 Im[a5] Re[a2]^3 Re[a5]^2-6 a1 a4^2 Re[a3] Re[a5]^2+72 a1^2 a6 Re[a3] Re[a5]^2+24 a1 a4^2 t^2 Re[a3] Re[a5]^2-288 a1^2 a6 t^2 Re[a3] Re[a5]^2+72 a1 a4^2 t^4 Re[a3] Re[a5]^2-864 a1^2 a6 t^4 Re[a3] Re[a5]^2-24 a1 a4^2 t^6 Re[a3] Re[a5]^2+288 a1^2 a6 t^6 Re[a3] Re[a5]^2-132 a1 a4^2 t^8 Re[a3] Re[a5]^2+1584 a1^2 a6 t^8 Re[a3] Re[a5]^2-24 a1 a4^2 t^10 Re[a3] Re[a5]^2+288 a1^2 a6 t^10 Re[a3] Re[a5]^2+72 a1 a4^2 t^12 Re[a3] Re[a5]^2-864 a1^2 a6 t^12 Re[a3] Re[a5]^2+24 a1 a4^2 t^14 Re[a3] Re[a5]^2-288 a1^2 a6 t^14 Re[a3] Re[a5]^2-6 a1 a4^2 t^16 Re[a3] Re[a5]^2+72 a1^2 a6 t^16 Re[a3] Re[a5]^2-216 a1 t Im[a5] Re[a2] Re[a3] Re[a5]^2+1512 a1 t^3 Im[a5] Re[a2] Re[a3] Re[a5]^2-1080 a1 t^5 Im[a5] Re[a2] Re[a3] Re[a5]^2-2808 a1 t^7 Im[a5] Re[a2] Re[a3] Re[a5]^2+2808 a1 t^9 Im[a5] Re[a2] Re[a3] Re[a5]^2+1080 a1 t^11 Im[a5] Re[a2] Re[a3] Re[a5]^2-1512 a1 t^13 Im[a5] Re[a2] Re[a3] Re[a5]^2+216 a1 t^15 Im[a5] Re[a2] Re[a3] Re[a5]^2+4 a4 Re[a2]^2 Re[a3] Re[a5]^2-32 a4 t^2 Re[a2]^2 Re[a3] Re[a5]^2+48 a4 t^4 Re[a2]^2 Re[a3] Re[a5]^2+32 a4 t^6 Re[a2]^2 Re[a3] Re[a5]^2-104 a4 t^8 Re[a2]^2 Re[a3] Re[a5]^2+32 a4 t^10 Re[a2]^2 Re[a3] Re[a5]^2+48 a4 t^12 Re[a2]^2 Re[a3] Re[a5]^2-32 a4 t^14 Re[a2]^2 Re[a3] Re[a5]^2+4 a4 t^16 Re[a2]^2 Re[a3] Re[a5]^2-12 a1 a4 Re[a3]^2 Re[a5]^2+144 a1 a4 t^2 Re[a3]^2 Re[a5]^2-432 a1 a4 t^4 Re[a3]^2 Re[a5]^2-144 a1 a4 t^6 Re[a3]^2 Re[a5]^2+888 a1 a4 t^8 Re[a3]^2 Re[a5]^2-144 a1 a4 t^10 Re[a3]^2 Re[a5]^2-432 a1 a4 t^12 Re[a3]^2 Re[a5]^2+144 a1 a4 t^14 Re[a3]^2 Re[a5]^2-12 a1 a4 t^16 Re[a3]^2 Re[a5]^2+4 Re[a2]^2 Re[a3]^2 Re[a5]^2-64 t^2 Re[a2]^2 Re[a3]^2 Re[a5]^2+368 t^4 Re[a2]^2 Re[a3]^2 Re[a5]^2-960 t^6 Re[a2]^2 Re[a3]^2 Re[a5]^2+1304 t^8 Re[a2]^2 Re[a3]^2 Re[a5]^2-960 t^10 Re[a2]^2 Re[a3]^2 Re[a5]^2+368 t^12 Re[a2]^2 Re[a3]^2 Re[a5]^2-64 t^14 Re[a2]^2 Re[a3]^2 Re[a5]^2+4 t^16 Re[a2]^2 Re[a3]^2 Re[a5]^2-8 a1 Re[a3]^3 Re[a5]^2+160 a1 t^2 Re[a3]^3 Re[a5]^2-1184 a1 t^4 Re[a3]^3 Re[a5]^2+3936 a1 t^6 Re[a3]^3 Re[a5]^2-5808 a1 t^8 Re[a3]^3 Re[a5]^2+3936 a1 t^10 Re[a3]^3 Re[a5]^2-1184 a1 t^12 Re[a3]^3 Re[a5]^2+160 a1 t^14 Re[a3]^3 Re[a5]^2-8 a1 t^16 Re[a3]^3 Re[a5]^2+216 a1^2 t Im[a5] Re[a5]^3+216 a1^2 t^3 Im[a5] Re[a5]^3-648 a1^2 t^5 Im[a5] Re[a5]^3-648 a1^2 t^7 Im[a5] Re[a5]^3+648 a1^2 t^9 Im[a5] Re[a5]^3+648 a1^2 t^11 Im[a5] Re[a5]^3-216 a1^2 t^13 Im[a5] Re[a5]^3-216 a1^2 t^15 Im[a5] Re[a5]^3+18 a1 a4 Re[a2] Re[a5]^3-72 a1 a4 t^4 Re[a2] Re[a5]^3+108 a1 a4 t^8 Re[a2] Re[a5]^3-72 a1 a4 t^12 Re[a2] Re[a5]^3+18 a1 a4 t^16 Re[a2] Re[a5]^3-16 Re[a2]^3 Re[a5]^3+64 t^2 Re[a2]^3 Re[a5]^3-64 t^4 Re[a2]^3 Re[a5]^3-64 t^6 Re[a2]^3 Re[a5]^3+160 t^8 Re[a2]^3 Re[a5]^3-64 t^10 Re[a2]^3 Re[a5]^3-64 t^12 Re[a2]^3 Re[a5]^3+64 t^14 Re[a2]^3 Re[a5]^3-16 t^16 Re[a2]^3 Re[a5]^3+36 a1 Re[a2] Re[a3] Re[a5]^3-288 a1 t^2 Re[a2] Re[a3] Re[a5]^3+432 a1 t^4 Re[a2] Re[a3] Re[a5]^3+288 a1 t^6 Re[a2] Re[a3] Re[a5]^3-936 a1 t^8 Re[a2] Re[a3] Re[a5]^3+288 a1 t^10 Re[a2] Re[a3] Re[a5]^3+432 a1 t^12 Re[a2] Re[a3] Re[a5]^3-288 a1 t^14 Re[a2] Re[a3] Re[a5]^3+36 a1 t^16 Re[a2] Re[a3] Re[a5]^3-27 a1^2 Re[a5]^4+108 a1^2 t^4 Re[a5]^4-162 a1^2 t^8 Re[a5]^4+108 a1^2 t^12 Re[a5]^4-27 a1^2 t^16 Re[a5]^4+512 t^3 (-1+t^2)^3 Im[a3]^3 (-4 a1 t^2 Im[a5]^2-a6 (-1+t^2)^2 Re[a2]^2-4 a1 t (-1+t^2) Im[a5] Re[a5]+a1 (4 a4 a6 (1+t^2)^2+8 a6 (1-6 t^2+t^4) Re[a3]-(-1+t^2)^2 Re[a5]^2))+16 t^3 (1+t^2)^2 Im[a2]^3 (-64 t^3 Im[a5]^3-96 t^2 (-1+t^2) Im[a5]^2 Re[a5]+6 t Im[a5] (3 a4 a6+6 a4 a6 t^2+3 a4 a6 t^4+24 a6 t (-1+t^2) Im[a3]+6 a6 (1-6 t^2+t^4) Re[a3]-8 Re[a5]^2+16 t^2 Re[a5]^2-8 t^4 Re[a5]^2)-(-1+t^2) (54 a6^2 (1+t^2)^2 Re[a2]+Re[a5] (-9 a4 a6-18 a4 a6 t^2-9 a4 a6 t^4-72 a6 t (-1+t^2) Im[a3]-18 a6 (1-6 t^2+t^4) Re[a3]+8 Re[a5]^2-16 t^2 Re[a5]^2+8 t^4 Re[a5]^2)))-64 t^2 (-1+t^2)^2 Im[a3]^2 (4 t^2 Im[a5]^2 (3 a1 a4 (1+t^2)^2-(-1+t^2)^2 Re[a2]^2+6 a1 (1-6 t^2+t^4) Re[a3])+20 a1 a6 (-1+t^4)^2 Re[a2] Re[a5]+4 t (-1+t^2) Im[a5] (10 a1 a6 (1+t^2)^2 Re[a2]-(-1+t^2)^2 Re[a2]^2 Re[a5]+3 a1 (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3]) Re[a5])+(-1+t^2)^2 Re[a2]^2 (3 a4 a6 (1+t^2)^2+6 a6 (1-6 t^2+t^4) Re[a3]-(-1+t^2)^2 Re[a5]^2)+a1 (2 a6 (-3 a4^2+4 a1 a6) (1+t^2)^4-24 a6 (1-6 t^2+t^4)^2 Re[a3]^2+3 a4 (-1+t^4)^2 Re[a5]^2-6 (1-6 t^2+t^4) Re[a3] (4 a4 a6 (1+t^2)^2-(-1+t^2)^2 Re[a5]^2)))-8 t (-1+t^2) Im[a3] (-144 a1 t^3 (-1+t^2) (1+t^2)^2 Im[a5]^3 Re[a2]-18 a6 (-1+t^2)^4 (1+t^2)^2 Re[a2]^3 Re[a5]-4 t^2 Im[a5]^2 (2 (-1+t^2)^2 Re[a2]^2 (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3])+3 a1 (-((a4^2-12 a1 a6) (1+t^2)^4)-4 a4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3]-4 (1-6 t^2+t^4)^2 Re[a3]^2)+54 a1 (-1+t^4)^2 Re[a2] Re[a5])+2 a1 (-1+t^4)^2 Re[a2] Re[a5] (20 a4 a6 (1+t^2)^2+40 a6 (1-6 t^2+t^4) Re[a3]-9 (-1+t^2)^2 Re[a5]^2)-4 t (-1+t^2) Im[a5] (9 a6 (-1+t^4)^2 Re[a2]^3+2 (-1+t^2)^2 Re[a2]^2 (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3]) Re[a5]+3 a1 (-((a4^2-12 a1 a6) (1+t^2)^4)-4 a4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3]-4 (1-6 t^2+t^4)^2 Re[a3]^2) Re[a5]-a1 (1+t^2)^2 Re[a2] (20 a4 a6 (1+t^2)^2+40 a6 (1-6 t^2+t^4) Re[a3]-27 (-1+t^2)^2 Re[a5]^2))+(-1+t^2)^2 Re[a2]^2 (3 a6 (a4^2-12 a1 a6) (1+t^2)^4+12 a6 (1-6 t^2+t^4)^2 Re[a3]^2-2 a4 (-1+t^4)^2 Re[a5]^2+4 (1-6 t^2+t^4) Re[a3] (3 a4 a6 (1+t^2)^2-(-1+t^2)^2 Re[a5]^2))+a1 (-4 a4 a6 (a4^2-4 a1 a6) (1+t^2)^6-32 a6 (1-6 t^2+t^4)^3 Re[a3]^3+3 (a4^2-12 a1 a6) (-1+t^2)^2 (1+t^2)^4 Re[a5]^2-12 (1-6 t^2+t^4)^2 Re[a3]^2 (4 a4 a6 (1+t^2)^2-(-1+t^2)^2 Re[a5]^2)-4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3] (2 a6 (3 a4^2-4 a1 a6) (1+t^2)^2-3 a4 (-1+t^2)^2 Re[a5]^2)))-4 t^2 Im[a2]^2 (a4^3 a6-36 a1 a4 a6^2+6 a4^3 a6 t^2-216 a1 a4 a6^2 t^2+15 a4^3 a6 t^4-540 a1 a4 a6^2 t^4+20 a4^3 a6 t^6-720 a1 a4 a6^2 t^6+15 a4^3 a6 t^8-540 a1 a4 a6^2 t^8+6 a4^3 a6 t^10-216 a1 a4 a6^2 t^10+a4^3 a6 t^12-36 a1 a4 a6^2 t^12+512 a6 t^3 (-1+t^2)^3 Im[a3]^3+384 t^3 (-1+t^2) (1+t^2)^2 Im[a5]^3 Re[a2]+162 a6^2 Re[a2]^2+324 a6^2 t^2 Re[a2]^2-162 a6^2 t^4 Re[a2]^2-648 a6^2 t^6 Re[a2]^2-162 a6^2 t^8 Re[a2]^2+324 a6^2 t^10 Re[a2]^2+162 a6^2 t^12 Re[a2]^2+6 a4^2 a6 Re[a3]-72 a1 a6^2 Re[a3]-12 a4^2 a6 t^2 Re[a3]+144 a1 a6^2 t^2 Re[a3]-102 a4^2 a6 t^4 Re[a3]+1224 a1 a6^2 t^4 Re[a3]-168 a4^2 a6 t^6 Re[a3]+2016 a1 a6^2 t^6 Re[a3]-102 a4^2 a6 t^8 Re[a3]+1224 a1 a6^2 t^8 Re[a3]-12 a4^2 a6 t^10 Re[a3]+144 a1 a6^2 t^10 Re[a3]+6 a4^2 a6 t^12 Re[a3]-72 a1 a6^2 t^12 Re[a3]+12 a4 a6 Re[a3]^2-120 a4 a6 t^2 Re[a3]^2+180 a4 a6 t^4 Re[a3]^2+624 a4 a6 t^6 Re[a3]^2+180 a4 a6 t^8 Re[a3]^2-120 a4 a6 t^10 Re[a3]^2+12 a4 a6 t^12 Re[a3]^2+8 a6 Re[a3]^3-144 a6 t^2 Re[a3]^3+888 a6 t^4 Re[a3]^3-2016 a6 t^6 Re[a3]^3+888 a6 t^8 Re[a3]^3-144 a6 t^10 Re[a3]^3+8 a6 t^12 Re[a3]^3-54 a4 a6 Re[a2] Re[a5]-108 a4 a6 t^2 Re[a2] Re[a5]+54 a4 a6 t^4 Re[a2] Re[a5]+216 a4 a6 t^6 Re[a2] Re[a5]+54 a4 a6 t^8 Re[a2] Re[a5]-108 a4 a6 t^10 Re[a2] Re[a5]-54 a4 a6 t^12 Re[a2] Re[a5]-108 a6 Re[a2] Re[a3] Re[a5]+648 a6 t^2 Re[a2] Re[a3] Re[a5]+108 a6 t^4 Re[a2] Re[a3] Re[a5]-1296 a6 t^6 Re[a2] Re[a3] Re[a5]+108 a6 t^8 Re[a2] Re[a3] Re[a5]+648 a6 t^10 Re[a2] Re[a3] Re[a5]-108 a6 t^12 Re[a2] Re[a3] Re[a5]-a4^2 Re[a5]^2+6 a1 a6 Re[a5]^2-2 a4^2 t^2 Re[a5]^2+12 a1 a6 t^2 Re[a5]^2+a4^2 t^4 Re[a5]^2-6 a1 a6 t^4 Re[a5]^2+4 a4^2 t^6 Re[a5]^2-24 a1 a6 t^6 Re[a5]^2+a4^2 t^8 Re[a5]^2-6 a1 a6 t^8 Re[a5]^2-2 a4^2 t^10 Re[a5]^2+12 a1 a6 t^10 Re[a5]^2-a4^2 t^12 Re[a5]^2+6 a1 a6 t^12 Re[a5]^2-4 a4 Re[a3] Re[a5]^2+24 a4 t^2 Re[a3] Re[a5]^2+4 a4 t^4 Re[a3] Re[a5]^2-48 a4 t^6 Re[a3] Re[a5]^2+4 a4 t^8 Re[a3] Re[a5]^2+24 a4 t^10 Re[a3] Re[a5]^2-4 a4 t^12 Re[a3] Re[a5]^2-4 Re[a3]^2 Re[a5]^2+56 t^2 Re[a3]^2 Re[a5]^2-252 t^4 Re[a3]^2 Re[a5]^2+400 t^6 Re[a3]^2 Re[a5]^2-252 t^8 Re[a3]^2 Re[a5]^2+56 t^10 Re[a3]^2 Re[a5]^2-4 t^12 Re[a3]^2 Re[a5]^2+48 Re[a2] Re[a5]^3-96 t^2 Re[a2] Re[a5]^3-48 t^4 Re[a2] Re[a5]^3+192 t^6 Re[a2] Re[a5]^3-48 t^8 Re[a2] Re[a5]^3-96 t^10 Re[a2] Re[a5]^3+48 t^12 Re[a2] Re[a5]^3-4 t^2 Im[a5]^2 ((a4^2-6 a1 a6) (1+t^2)^4+4 a4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3]+4 (1-6 t^2+t^4)^2 Re[a3]^2-144 (-1+t^4)^2 Re[a2] Re[a5])+64 t^2 (-1+t^2)^2 Im[a3]^2 (3 a4 a6+6 a4 a6 t^2+3 a4 a6 t^4-4 t^2 Im[a5]^2+6 a6 (1-6 t^2+t^4) Re[a3]-4 t (-1+t^2) Im[a5] Re[a5]-Re[a5]^2+2 t^2 Re[a5]^2-t^4 Re[a5]^2)-4 t (-1+t^2) Im[a5] (((a4^2-6 a1 a6) (1+t^2)^4+4 a4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3]+4 (1-6 t^2+t^4)^2 Re[a3]^2) Re[a5]+9 (1+t^2)^2 Re[a2] (3 a4 a6 (1+t^2)^2+6 a6 (1-6 t^2+t^4) Re[a3]-8 (-1+t^2)^2 Re[a5]^2))+8 t (-1+t^2) Im[a3] (12 a6 (1-6 t^2+t^4)^2 Re[a3]^2-8 t^2 Im[a5]^2 (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3])-4 t (-1+t^2) Im[a5] (27 a6 (1+t^2)^2 Re[a2]+2 (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3]) Re[a5])+4 (1-6 t^2+t^4) Re[a3] (3 a4 a6 (1+t^2)^2-(-1+t^2)^2 Re[a5]^2)+(1+t^2)^2 (3 a6 (a4^2-12 a1 a6) (1+t^2)^2-54 a6 (-1+t^2)^2 Re[a2] Re[a5]-2 a4 (-1+t^2)^2 Re[a5]^2)))-4 t Im[a2] (-24 t^3 (1+t^2)^2 Im[a5]^3 (3 a1 a4 (1+t^2)^2+24 a1 t (-1+t^2) Im[a3]-8 (-1+t^2)^2 Re[a2]^2+6 a1 (1-6 t^2+t^4) Re[a3])-4 t^2 (-1+t^2) Im[a5]^2 (Re[a2] ((a4^2-6 a1 a6) (1+t^2)^4+64 t^2 (-1+t^2)^2 Im[a3]^2+4 a4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3]+4 (1-6 t^2+t^4)^2 Re[a3]^2+16 t (-1+t^2) Im[a3] (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3]))-72 (-1+t^4)^2 Re[a2]^2 Re[a5]+27 a1 (1+t^2)^2 (a4 (1+t^2)^2+8 t (-1+t^2) Im[a3]+2 (1-6 t^2+t^4) Re[a3]) Re[a5])+2 t Im[a5] (-2 (-1+t^2)^2 Re[a2] ((a4^2-6 a1 a6) (1+t^2)^4+4 a4 (1+t^2)^2 (1-6 t^2+t^4) Re[a3]+4 (1-6 t^2+t^4)^2 Re[a3]^2) Re[a5]+128 t^2 (-1+t^2)^2 Im[a3]^2 (5 a1 a6 (1+t^2)^2-(-1+t^2)^2 Re[a2] Re[a5])-9 (-1+t^4)^2 Re[a2]^2 (3 a4 a6 (1+t^2)^2+6 a6 (1-6 t^2+t^4) Re[a3]-8 (-1+t^2)^2 Re[a5]^2)+a1 (1+t^2)^2 (2 a6 (5 a4^2+12 a1 a6) (1+t^2)^4+40 a6 (1-6 t^2+t^4)^2 Re[a3]^2-27 a4 (-1+t^4)^2 Re[a5]^2+2 (1-6 t^2+t^4) Re[a3] (20 a4 a6 (1+t^2)^2-27 (-1+t^2)^2 Re[a5]^2))+8 t (-1+t^2) Im[a3] (-27 a6 (-1+t^4)^2 Re[a2]^2-4 (-1+t^2)^2 Re[a2] (a4 (1+t^2)^2+2 (1-6 t^2+t^4) Re[a3]) Re[a5]+a1 (1+t^2)^2 (20 a4 a6 (1+t^2)^2+40 a6 (1-6 t^2+t^4) Re[a3]-27 (-1+t^2)^2 Re[a5]^2)))+(-1+t^2) (54 a6^2 (-1+t^2)^2 (1+t^2)^4 Re[a2]^3-3 (-1+t^4)^2 Re[a2]^2 Re[a5] (9 a4 a6+18 a4 a6 t^2+9 a4 a6 t^4+72 a6 t (-1+t^2) Im[a3]+18 a6 (1-6 t^2+t^4) Re[a3]-8 Re[a5]^2+16 t^2 Re[a5]^2-8 t^4 Re[a5]^2)+a1 (1+t^2)^2 Re[a5] (2 a6 (5 a4^2+12 a1 a6) (1+t^2)^4+640 a6 t^2 (-1+t^2)^2 Im[a3]^2+40 a6 (1-6 t^2+t^4)^2 Re[a3]^2-9 a4 (-1+t^4)^2 Re[a5]^2+2 (1-6 t^2+t^4) Re[a3] (20 a4 a6 (1+t^2)^2-9 (-1+t^2)^2 Re[a5]^2)+8 t (-1+t^2) Im[a3] (20 a4 a6 (1+t^2)^2+40 a6 (1-6 t^2+t^4) Re[a3]-9 (-1+t^2)^2 Re[a5]^2))+Re[a2] (a4 a6 (a4^2-36 a1 a6) (1+t^2)^6+512 a6 t^3 (-1+t^2)^3 Im[a3]^3+8 a6 (1-6 t^2+t^4)^3 Re[a3]^3-(a4^2-6 a1 a6) (-1+t^2)^2 (1+t^2)^4 Re[a5]^2+4 (1-6 t^2+t^4)^2 Re[a3]^2 (3 a4 a6 (1+t^2)^2-(-1+t^2)^2 Re[a5]^2)+64 t^2 (-1+t^2)^2 Im[a3]^2 (3 a4 a6 (1+t^2)^2+6 a6 (1-6 t^2+t^4) Re[a3]-(-1+t^2)^2 Re[a5]^2)+2 (1+t^2)^2 (1-6 t^2+t^4) Re[a3] (3 a6 (a4^2-12 a1 a6) (1+t^2)^2-2 a4 (-1+t^2)^2 Re[a5]^2)+8 t (-1+t^2) Im[a3] (3 a6 (a4^2-12 a1 a6) (1+t^2)^4+12 a6 (1-6 t^2+t^4)^2 Re[a3]^2-2 a4 (-1+t^4)^2 Re[a5]^2+4 (1-6 t^2+t^4) Re[a3] (3 a4 a6 (1+t^2)^2-(-1+t^2)^2 Re[a5]^2))))));
Return[expression]]

(*Functions to generate polynomials g1,g2,g3 and g4 from c coefficients*)
genG1[{c1_,c2_,c3_,c4_,c5_,c6_}]:=Module[{g1},
g1 = 4c1*c6*\[Chi][t,c3,c4+2Sqrt[c1*c6]]-(\[CapitalLambda][t,Sqrt[c1]*c5-Sqrt[c6]*c2])^2;
Return[Simplify[g1]]]
genG4[{c1_,c2_,c3_,c4_,c5_,c6_}]:=Module[{g4},
g4 = 4c1*c6*\[Chi][t,c3,c4-2Sqrt[c1*c6]]-(\[CapitalLambda][t,Sqrt[c1]*c5+Sqrt[c6]*c2])^2;
Return[Simplify[g4]]]
genG2[{c1_,c2_,c3_,c4_,c5_,c6_}]:=Module[{g2},
g2= \[Chi][t,c3,c4+2Sqrt[c1*c6]];
Return[Simplify[g2]]]
genG3[{c1_,c2_,c3_,c4_,c5_,c6_}]:=Module[{g3},
g3= \[Chi][t,-c3,-c4+6Sqrt[c1*c6]];
Return[Simplify[g3]]]

(*Function Evaluating the main line of the determinant criterion*)
detXwCondition[coeffs_]:=Module[{g1,g2,g3,g4,gdel,con1,con2,con3,con4},
If[Or[coeffs[[1]]<0,coeffs[[-1]]<0] ,Return[False]];
If[trivialConditions[coeffs],Return[True]];
g1 = genG1[coeffs];
g2 = genG2[coeffs];
g3 = genG3[coeffs];
g4 = genG4[coeffs];
gdel = genfdeltaPoly[coeffs];
con1 =polynomialNonnegativityQ[gdel];
con2 = polynomialNonnegativityQ[g1];
con3 = polynomialNonnegativityQ[g2];
con4 = twoPolyForFullDomain[g3,g4];
If[con4, con4 = twoPolyNonnegativityQ[g3,g4,-100,100]];
Return[And[con1,con2,con3,con4]]]

(*Trivial conditions on the coefficients*)
trivialConditions[{c1_,c2_,c3_,c4_,c5_,c6_},var_:t]:=Module[{conda,condb,condc,condd},
		conda = {c1,c2,c3,c4,c5,c6}=={0,0,0,0,0,0};
		condb = And[{c2,c3,c4,c5,c6}=={0,0,0,0,0},c1>0];
		condc = And[{c2,c3,c4,c5,c1}=={0,0,0,0,0},c6>0];
		condd = And[{c2,c1,c5,c6}=={0,0,0,0},polynomialNonnegativityQ[\[Chi][var,c3,c4]]];
		Return[Or[conda,condb,condc,condd]]]

(*Trace condition*)
trXwContidtionQ[m_]:= Module[{\[Tau]1,\[Tau]2,\[Rho],con1,con2},
\[Tau]1 = m[[1,1]]+m[[3,3]];
\[Tau]2 = m[[2,2]]+m[[4,4]];
\[Rho]=m[[1,2]]+m[[4,3]];
con1 = Tr[m]>=0;
con2 = (\[Tau]1*\[Tau]2 >=\[Rho]*Conjugate[\[Rho]]);
Return[And[con1,con2]]]


trXwContidtion2Q[m_]:= Module[{\[Tau]1,\[Tau]2,\[Rho],con1,con2},
\[Tau]1 = m[[1,1]]+m[[3,3]];
\[Tau]2 = m[[2,2]]+m[[4,4]];
\[Rho]=m[[1,2]]+m[[4,3]];
con1 = -4 \[Rho]^2-\[Tau]1^2+\[Tau]1 Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2]+2 \[Tau]1 \[Tau]2+Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2] \[Tau]2-\[Tau]2^2>=0;
con2 = 4 \[Rho]^2+\[Tau]1^2+\[Tau]1 Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2]-2 \[Tau]1 \[Tau]2+Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2] \[Tau]2+\[Tau]2^2>=0;
Return[{And[con1,con2],-4 \[Rho]^2-\[Tau]1^2+\[Tau]1 Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2]+2 \[Tau]1 \[Tau]2+Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2] \[Tau]2-\[Tau]2^2,4 \[Rho]^2+\[Tau]1^2+\[Tau]1 Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2]-2 \[Tau]1 \[Tau]2+Sqrt[4 \[Rho]^2+(\[Tau]1-\[Tau]2)^2] \[Tau]2+\[Tau]2^2}]]

(*Function to check Block - Positivity of an 4x4 Operator - To be finished*)
blockPositivityQ[m_]:=Module[{coeffs,con1,con2},
coeffs = cCoefficients[m];
con1 = detXwCondition[coeffs];
con2 = trXwContidtionQ[m];
Return[And[con1,con2]]]

blockPositivity2Q[m_]:=Module[{coeffs,con1,con2},
coeffs = cCoefficients[m];
con1 = detXwCondition[coeffs];
con2 = trXwContidtion2Q[m][[1]];
Return[And[con1,con2]]]


Begin["`Private`"];


End[];


EndPackage[];
