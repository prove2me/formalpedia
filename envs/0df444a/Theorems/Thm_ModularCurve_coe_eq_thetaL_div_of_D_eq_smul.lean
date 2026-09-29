-- Prove2me | Theorems.Thm_ModularCurve_coe_eq_thetaL_div_of_D_eq_smul
-- name    : ModularCurve.coe_eq_thetaL_div_of_D_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/142fdf1f-75ee-553f-a985-98c78e20fe76
-- title:
--   Ratio of differentials read off q-expansions
-- statement:
--   Let $K$ be a field and let $F$ be an intermediate field of the extension $K((q))/K$, where $K((q))$ is the field of formal Laurent series over $K$; the operator $\theta$ on $K((q))$, written [`ModularCurve.thetaL`](def/ModularCurve_QExpansionDiff.html#L16), is the $K((q))$-linear map sending a Laurent series $h$ to $q \cdot h'$, that is, the product of the Hahn series $\mathrm{single}(1,1)$ with the formal derivative of $h$ (so $\theta = q\,d/dq$). Let $f, g, c_0$ be elements of $F$ and assume that in the module of Kähler differentials of $F$ over $K$ the relation $D f = c_0 \cdot D g$ holds, where $D$ is the universal $K$-derivation of $F$. Assume further that $\theta(g) \neq 0$, $g$ being viewed as an element of $K((q))$. Then the image of $c_0$ in $K((q))$ equals the quotient $\theta(f)/\theta(g)$ of Laurent series.
--
--   This records that the ratio of two differentials on a subfield of $K((q))$ may be computed from $q$-expansions, $\theta = q\,d/dq$ being a $K$-derivation of $K((q))$ whose restriction to $F$ factors through the universal derivation. It is used in the computation of ramification indices and orders of vanishing at places of modular curves, in [`ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le`](thm.html#ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le) and [`ModularCurve.six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace`](thm.html#ModularCurve.six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_eq_thetaL_div_of_D_eq_smul.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Mathlib.FieldTheory.IntermediateField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.coe_eq_thetaL_div_of_D_eq_smul (K : Type*) [Field K]
    (F : IntermediateField K (LaurentSeries K)) (f g c₀ : F)
    (h : KaehlerDifferential.D K F f = c₀ • KaehlerDifferential.D K F g)
    (hg : ModularCurve.thetaL K (g : LaurentSeries K) ≠ 0) :
    (c₀ : LaurentSeries K) =
      ModularCurve.thetaL K (f : LaurentSeries K) / ModularCurve.thetaL K (g : LaurentSeries K) := by sorry
