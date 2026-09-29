-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
-- name    : ModularCurve.PlaceSpecialization.redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ca10e967-81e8-59b3-8fdf-18588f1ea818
-- title:
--   Second level-one reduction at a place with integral j_q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Fix further `data`, consisting of a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions, together with `hKr`, the assertion that $\Phi$ reduces modulo $q$ to $(X^q-Y)(X-Y^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two level-raising algebra maps $\overline{\mathbb Q}\!\cdot\!\mathcal F(1)\to\overline{\mathbb Q}\!\cdot\!\mathcal F(q)$. Let $P$ be a place specialisation for these data: in particular it supplies a map $\mathrm{sp}$ from places of `modularFunctionFieldBar 1` to places of `modularFunctionFieldC k 1` whose clause `d0_j` sends a place where $j-a$ has positive order ($a\in A$) to a place where $j-\mathrm{red}(a)$ has positive order. Let $W$ be a place of `modularFunctionFieldBar (1 * q)` and $b\in A$, and assume $\mathrm{ord}_W\bigl(\beta(j)-b\bigr)>0$, where $\beta$ is `heckeBetaBar` and $\mathrm{ord}$ is minus the logarithm of the associated adic valuation. Then $P$'s second reduction of $W$, namely $\mathrm{sp}$ applied to the restriction of $W$ along $\beta$, equals `charLGeomPlaceOfPoint k (red b)`, the place $j=\mathrm{red}(b)$ of $k(j)$.
--
--   This identifies the second (that is, $j_q$-side) reduction of a place of the level-$q$ modular function field as the place of the $j$-line over $k$ at the reduction of its $j_q$-coordinate, so that an abstract place specialisation is pinned down to "reduce the coordinate". It is used throughout the level-one gluing arguments, for instance in the divisor laws for prolongation pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_LevelOneGlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (b : A)
    (hW : 0 < W.ord (heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (b : AlgebraicClosure ℚ))) :
    P.redSnd W = charLGeomPlaceOfPoint k (red b) := by sorry
