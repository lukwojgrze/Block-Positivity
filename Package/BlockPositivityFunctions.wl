(* ::Package:: *)

BeginPackage["BlockPositivityFunctions`"];





(*Function to check Block - Positivity of an 4x4 Operator - To be finished*)
blockPositivityQ[m_]:=Module[{coeffs,con1,con2},
coeffs = cCoefficients[m];
con1 = detXwMainConditionQ[coeffs];
con2 = trXwContidtionQ[m];
Return[And[con1,con2]]]

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
(*Function to check nonnegativity of two polynomials on an interval (a,b)*)
twoPolyNonnegativityQ[g1_,g2_,a_,b_,var_:t]:=Module[{intervalMesh ,i,test},
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
genfdeltaPoly[{a1_,a2_,a3_,a4_,a5_,a6_}]:=Module[{alpha,beta,gamma,f,w,expression},
W[r_,t_,c1_,c2_,c3_,c4_,c5_,c6_] := c1 (t^2+1)^2*r^4-2(t^2+1)\[CapitalLambda][t,c2]r^3+\[Chi][t,c3,c4]*r^2-2(t^2+1)\[CapitalLambda][t,c5]*r+c6 (t^2+1)^2;

\[Alpha][P_,t_]:=Coefficient[P,t,3]*(Coefficient[P,t,4])^(-3/4)*(Coefficient[P,t,0])^(-1/4);
\[Beta][P_,t_]:=Coefficient[P,t,2]*(Coefficient[P,t,4])^(-1/2)*(Coefficient[P,t,0])^(-1/2);
\[Gamma][P_,t_]:=Coefficient[P,t,1]*(Coefficient[P,t,4])^(-1/4)*(Coefficient[P,t,0])^(-3/4);
w = W[r,t,a1,a2,a3,a4,a5,a6];
alpha = Simplify[\[Alpha][w,r],Element[t,Reals]];
beta = Simplify[\[Beta][w,r],Element[t,Reals]];
gamma = Simplify[\[Gamma][w,r],Element[t,Reals]];
f = r^4+alpha*r^3+beta*r^2*gamma*r+1;
expression = Simplify[Discriminant[f,r]]*a1^3 a6^5 (1+t^2)^12;
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
detXwMainConditionQ[coeffs_]:=Module[{g1,g2,g3,g4,gdel,con1,con2,con3,con4},
g1 = genG1[coeffs]*1.;
g2 = genG2[coeffs]*1.;
g3 = genG3[coeffs]*1.;
g4 = genG4[coeffs]*1.;
gdel = genfdeltaPoly[coeffs];
con1 =polynomialNonnegativityQ[gdel];
con2 = polynomialNonnegativityQ[g1];
con3 = polynomialNonnegativityQ[g2];
con4 = twoPolyNonnegativityQ[g3,g4,-1000,1000];
Return[And[con1,con2,con3,con4]]]
(*Trace condition*)
trXwContidtionQ[m_]:= Module[{\[Tau]1,\[Tau]2,\[Rho],con1,con2},
\[Tau]1 = m[[1,1]]+m[[3,3]];
\[Tau]2 = m[[2,2]]+m[[4,4]];
\[Rho]=m[[1,2]]+m[[4,3]];
con1 = Tr[m]>=0;
con2 = (\[Tau]1*\[Tau]2 >=\[Rho]*Conjugate[\[Rho]]);
Return[And[con1,con2]]]


Begin["`Private`"];


End[];


EndPackage[];
