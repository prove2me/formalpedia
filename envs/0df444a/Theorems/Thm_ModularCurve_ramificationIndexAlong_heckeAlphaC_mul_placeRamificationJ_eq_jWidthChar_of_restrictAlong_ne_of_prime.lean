-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime
-- name    : ModularCurve.ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/0967e4a2-2aaf-51e2-82c9-fca110555242
-- title:
--   Off-diagonal roof places: e_α· r equals characteristic j-width
-- statement:
--   Let $M,s,q'$ be natural numbers with $M,s$ nonzero, $s$ and $q'$ prime, $s \neq q'$, $q' \nmid M$ and $s \nmid M$, and let $k$ be an algebraically closed field of characteristic $q'$. Inside the Laurent series field over $k$, let $F =$ `modularFunctionFieldC k M` and let `charLDegeneracyRoof k M s` be the intermediate field generated over $k$ by the expansions $j(q)$, $j(q^M)$, $j(q^{s})$ and $j(q^{Ms})$; write $\alpha =$ `heckeAlphaC` for the inclusion $F \hookrightarrow$ roof and $\beta =$ `heckeBetaC` for the map induced by $q \mapsto q^{s}$, both assumed to be integral ring maps (`HeckeAlphaCIntegral`, `HeckeBetaCIntegral`). Let $y$ be a place of the roof, that is a proper valuation subring containing $k$ whose ring is a principal ideal ring, and let $y_\alpha, y_\beta$ be the places of $F$ obtained by pulling the valuation subring back along $\alpha$, resp. $\beta$. Assume $y_\beta \neq y_\alpha$ and that $r =$ `placeRamificationJ M` $y_\alpha$, the (nonnegative part of the) order at $y_\alpha$ of $j - y_\alpha(j)$ for $j =$ `jGeomGen k M`, is positive. Then the ramification index of $y$ along $\alpha$ — the least $n > 0$ of the form $\mathrm{ord}_y(\alpha f)$ with $0 \neq f \in F$ — satisfies $e_\alpha(y)\, r =$ `jWidthChar` $q'\,(y_\alpha(j))$, which is $12$ or $1$ when $q' = 2$ according as $y_\alpha(j) = 0$ or not, $6$ or $1$ likewise when $q' = 3$, and `jWidth` of $y_\alpha(j)$ otherwise.
--
--   This is the full-ramification statement for places of the level-$M$ degree-$s$ degeneracy roof lying over an affine place of the $j$-line whose two degeneracy restrictions differ: such a place is ramified over the $j$-line to the full characteristic-$q'$ width of the corresponding $j$-invariant. It feeds the divisibility of the off-diagonal coefficients of the correspondence $\beta_*\alpha^*$ by the place width, used in the characteristic-$q'$ analysis of the Hecke correspondence on modular function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem
ModularCurve.ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (y : Place k ↥(charLDegeneracyRoof k M s))
    (hne : y.restrictAlong (heckeBetaC k M s) hβ ≠ y.restrictAlong (heckeAlphaC k M s) hα)
    (hr : 0 < placeRamificationJ M (y.restrictAlong (heckeAlphaC k M s) hα)) :
    y.ramificationIndexAlong (heckeAlphaC k M s)
        * placeRamificationJ M (y.restrictAlong (heckeAlphaC k M s) hα)
      = jWidthChar q' ((y.restrictAlong (heckeAlphaC k M s) hα).evalAt (jGeomGen k M)) := by sorry
