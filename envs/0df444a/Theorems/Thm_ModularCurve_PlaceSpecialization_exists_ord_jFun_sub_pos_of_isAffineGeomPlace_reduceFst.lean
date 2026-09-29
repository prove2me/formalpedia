-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
-- name    : ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/f731c979-2f3b-5fae-bd5d-6e3a3c708091
-- title:
--   A-value of j at places with affine first reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a natural number $N \neq 0$, an algebraically closed field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, let `hKr` assert the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$ in the relevant bivariate normalisation, and let `hα`, `hβ` assert that the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ into level $Nq$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` packet for these data, whose components include a map `sp` from places of $\overline{\mathbb Q}(X_0(N))$ (the field `modularFunctionFieldBar N`) to places of the characteristic-$q$ function field `modularFunctionFieldC k N`, together with the clauses `d0_j`, `d0_j_pole`, `d0_jN`, … relating $A$-values of the moduli coordinates upstairs to their $\mathrm{red}$-images downstairs. Let $Q$ be a place of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ — a proper valuation subring containing the base field whose ring is a principal ideal ring — and assume that its first reduction $P.\mathrm{reduceFst}\,Q$, obtained by restricting $Q$ along `heckeAlphaBar` and then applying `sp`, is an affine geometric place, that is, both `jGeomGen k N` and `jNGeomGen k N` lie in its valuation subring. Then there exists $a \in A$ such that the order of $\mathrm{jFun}\,N\,q - a$ at $Q$ is strictly positive and the order of `jGeomGen k N` $-\ \mathrm{red}(a)$ at $P.\mathrm{reduceFst}\,Q$ is strictly positive; here $\mathrm{jFun}\,N\,q$ is the $j$-function viewed in the level-$Nq$ field, and $\mathrm{ord}$ is $-\log$ of the adic valuation, so positivity means a zero.
--
--   The statement says that at a place of the level-$Nq$ modular function field whose first level-$N$ reduction is an affine point of the special fibre, the $j$-coordinate pulled back along the first degeneracy map takes a value in $A$, and that value reduces to the value of the geometric $j$-coordinate at the reduced place. It is used by the construction of chart data and of strict residue-disc coordinates on the models of $X_0(Nq)$ in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (haff : IsAffineGeomPlace k N (P.reduceFst Q)) :
    ∃ a : A, 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧
      0 < (P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a)) := by sorry
