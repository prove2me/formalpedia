-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne
-- name    : ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c997df88-f61c-5154-90cb-58b102efbf17
-- title:
--   Strict type one or two iff φ² moves `redFst`
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix data $data$ consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, together with the Kronecker congruence $hKr$ asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and fix the hypotheses $h\alpha$, $h\beta$ that the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialization of these data, carrying places of $\overline{\mathbb Q}$-modular function field of level $1$ to places of `modularFunctionFieldC k 1`, and let $W$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$. Write $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr`, the operator on places of `modularFunctionFieldC k 1` obtained by restricting a place to the Frobenius image subfield and transporting it back along the induced isomorphism, and write $r_1 W =$ `P.redFst W` $= P.sp(W$ restricted along `heckeAlphaBar`$)$ and $r_2 W =$ `P.redSnd W` for the two level-one reductions of $W$. The assertion is: the disjunction of $\bigl(\varphi(r_1W) = r_2W$ and $\varphi^2(r_1W) \ne r_1W\bigr)$ and $\bigl(r_1W = \varphi(r_2W)$ and $\varphi^2(r_2W) \ne r_2W\bigr)$ holds if and only if $\varphi^2(r_1 W) \ne r_1 W$.
--
--   This is the combinatorial criterion identifying, among the points of $X_0(q)$ in characteristic $q$, those that belong to one of the two strict types used by the level-one gluing datum: the excluded points are exactly those whose first reduced $j$-coordinate is fixed by the square of geometric Frobenius. It is used in the construction and analysis of level-one prolongation pairs, in particular in the existence of admissible good representatives and in the Riemann–Roch estimates for residue pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W) ↔
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
        ≠ P.redFst W := by sorry
