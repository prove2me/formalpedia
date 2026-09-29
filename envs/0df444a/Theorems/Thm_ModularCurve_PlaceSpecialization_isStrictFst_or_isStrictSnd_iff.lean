-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
-- name    : ModularCurve.PlaceSpecialization.isStrictFst_or_isStrictSnd_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/b37ec9d2-a6e4-5a70-920a-c0f70b12b817
-- title:
--   Strictness of a place versus φ²-fixedness of its first reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` consist of a monic $\Phi \in \mathbf Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$, and let `hα`, `hβ` assert that the two degeneracy algebra maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbf Q}$ are integral. Let $P$ be a `PlaceSpecialization` for these data, so in particular $P$ supplies a map `sp` from places of the level-$N$ function field `modularFunctionFieldBar N` over $\overline{\mathbf Q}$ to places of `modularFunctionFieldC k N`, a homomorphism on degree-zero divisor classes, and the compatibility axioms of that structure. Let $W$ be a place of `modularFunctionFieldBar (N*q)` over $\overline{\mathbf Q}$, and write $r_1W$, $r_2W$ for its two level-$N$ reductions, $r_1W = P.\mathrm{sp}$ applied to the restriction of $W$ along `heckeAlphaBar` (and $r_2W$ likewise along the second degeneracy map), and $\varphi$ for `frobOnPlacesGeomLevel k N data hKr`. The assertion is: $W$ is strict of the first kind ($\varphi(r_1W) = r_2W$ and $\varphi^2(r_1W) \neq r_1W$) or strict of the second kind ($r_1W = \varphi(r_2W)$ and $\varphi^2(r_2W) \neq r_2W$) if and only if $\varphi^2(r_1W) \neq r_1W$.
--
--   The two kinds of strictness record on which of the two components of the characteristic-$q$ special fibre of $X_0(Nq)$ a point lies, together with the requirement that its level-$N$ reduction not be a supersingular (i.e. $\varphi^2$-fixed) place; this equivalence replaces that disjunction by the single condition on $r_1W$. It is used to characterise good divisors by a condition on their support, and is cited further on in the construction of models and of the degree and component-group computations attached to a place specialization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff.lean

import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.isStrictFst_or_isStrictSnd_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.IsStrictFst W ∨ P.IsStrictSnd W) ↔
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W)) ≠ P.reduceFst W := by sorry
