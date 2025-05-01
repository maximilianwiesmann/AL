needsPackage "ReesAlgebra"

teraoModule = L -> (
    if #L != 0 then R := ring L#0;
    S := transpose jacobian matrix {L}; 
    D := diagonalMatrix L;
    K := ker map (R^(#L),, D|S); --redefines the degrees of the target to
                            -- be 0, and computes the degrees of the
                            -- source (from the target and source of
                            -- S,D) such that the map is
                            -- homogeneous. Specifying also the source
                            -- here would make the map non-homogeneous
                            -- again. If the degrees of the targets
                            -- are the same for S and D, D|S is also
                            -- homogeneous.
    K)

twoMatrices = L -> (
    K := teraoModule L;
    G := gens K;
    A := G^{0..(#L-1)};
    B := G^{(#L)..(numrows G)-1};
    (A,B))

newMatrix = L -> (
    if #L != 0 then R := ring L#0;
    J := transpose jacobian matrix {L}; 
    D := diagonalMatrix L;
    gg := gens R;
    n := numgens R;
    Q := baseRing(R);
    S := Q[join(gg, s_1..s_(#L)), Degrees => toList(join(n:{1,0}, #L:{0,1}))];
    Q2 := sub(D|J, S);
    ro := matrix {{s_1..s_(#L), n:0}};
    submatrix'(Q2||ro, , {0}))

detIdeal = A -> (
    Q := newMatrix A;
    m := numrows Q - 1; 
    n := numcols Q - (m-1);
    -- get the degrees of the f_i (from last col) and make the linear form
    esses := drop(gens ring Q, n);
    degs := first \ degree \ A;
    linform := matrix {degs} * transpose matrix {esses};  -- form linear form
    minors_(m+1) Q + ideal linform)

newMatrix' = L -> (
    if #L != 0 then R := ring L#0;
    J := transpose jacobian matrix {L}; 
    D := diagonalMatrix L;
    gg := gens R;
    n := numgens R;
    Q := baseRing(R);
    S := Q[join(gg, s_1..s_(#L)), Degrees => toList(join(n:{1,0}, #L:{0,1}))];
    Q2 := sub(D|J, S);
    ro := matrix {{s_1..s_(#L), n:0}};
    Q2||ro)


jacobianModule = L -> image (twoMatrices L)#1

logDerModule = L -> image (twoMatrices L)#0

likelihoodModule = L -> coker (twoMatrices L)#0 -- is a quotient of R^(#L)

preLikelihoodIdeal = L -> (
    if #L != 0 then R := ring L#0;
    A := (twoMatrices L)#0;
    gg := gens R;
    n := numgens R;
    Q := baseRing(R);
    S := Q[join(gg, s_1..s_(#L)), Degrees => toList(join(n:{1,0}, #L:{0,1}))];
    minors_1 (matrix{{s_1..s_(#L)}} * sub(A,S)))

likelihoodIdeal = L -> (    
    I0:=preLikelihoodIdeal L;
    I1:=I0;
    for f in L do I1 = saturate(I1, sub(f, ring I1));
    S := transpose jacobian matrix {L};
    -- need to compute the generic rank of S:
    Sr := sub (S, for i in gens ring S list i=>random(QQ));
    n := rank Sr;
    SL := sub(minors_n S, ring I1);
    saturate(I1,SL))

isTame = L -> (     -- naive implementation;
                    -- might need improvement due to computation of large determinants
    D := logDerModule L;
    R := ring D;
    Omega1 := Hom(D, R);
    OmegaPs := toList(1..rank(D)) / (i -> Hom(Hom(exteriorPower_i Omega1, R), R));
    PDs = OmegaPs / (OmegaP -> pdim OmegaP);
    all(PDs, 1..length(PDs), (d,p) -> d <= p)
)


-- Todo: Often one wants to call both and compare the ideals then the
--       results of the two ideal functions lie in different rings.
