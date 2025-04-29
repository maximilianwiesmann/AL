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
