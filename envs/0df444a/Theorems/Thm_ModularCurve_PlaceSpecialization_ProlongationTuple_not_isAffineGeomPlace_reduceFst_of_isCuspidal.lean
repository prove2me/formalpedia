-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/0b3a553a-a7bd-5e37-8158-136f0871e5c6
-- title:
--   Cuspidal places reduce to non-affine places on the first copy
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be modular polynomial data for level $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair of $q$-expansions), `hKr` the hypothesis that its bivariate reduction mod $q$ equals $(X^q - Y)(X - Y^q)$ in the relevant variables, and `hα`, `hβ` the hypotheses that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the level-$N$ function field into the level-$Nq$ function field over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` packet for these data, whose components include a map `sp` from places of $\overline{\mathbb Q}$-modular function field of level $N$ to places of the level-$N$ function field over $k$ together with compatibility clauses for $j$ and $j_N$. Let $V$ be a place of the level-$Nq$ modular function field over $\overline{\mathbb Q}$ which is cuspidal in the sense that $\operatorname{ord}_V(j - a) \le 0$ for every $a \in A$, where $j$ denotes `ProlongationTuple.jFun N q`. Then the place $P.\text{reduceFst}\,V$, obtained by restricting $V$ along `heckeAlphaBar` and applying `sp`, does not satisfy `IsAffineGeomPlace`, i.e. it is not the case that both generators `jGeomGen k N` and `jNGeomGen k N` lie in its valuation subring.
--
--   This is the statement that a place of the level-$Nq$ modular function field lying over a cusp specialises, under the first degeneracy map, to a place of the special fibre $X_0(N)_k$ at which $j$ has a pole, so that the reduced place lies outside the affine $j$-$j_N$ chart. It is used in the chart analysis of the special fibre of $X_0(Nq)$ in characteristic $q$, for instance to separate the cuspidal charts from the affine ones and in the verification of the model conditions on the reduced places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : ProlongationTuple.IsCuspidal P V) :
    ¬ IsAffineGeomPlace k N (P.reduceFst V) := by sorry
