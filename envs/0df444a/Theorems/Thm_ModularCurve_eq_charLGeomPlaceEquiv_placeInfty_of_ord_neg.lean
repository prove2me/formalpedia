-- Prove2me | Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
-- name    : ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/20bb87fd-12aa-5a9c-99ab-5e341e650672
-- title:
--   A place with a pole at jmath̃ is the place at infinity
-- statement:
--   Let $k$ be a field and consider the level-one modular function field `modularFunctionFieldC k 1`, the intermediate field of the Laurent series field $k((q))$ obtained by adjoining to $k$ the two elements `jqModC k` and `jqNModC k 1`, where `jqModC k` is the Laurent series $q^{-1}\cdot(\text{jNum})$, the $q$-expansion of the modular invariant with coefficients reduced into $k$ (the integral power series `jNum` being $E_4^3$ times the inverse of the relevant Dedekind eta unit). Let $v$ be a place of this field over $k$, that is, a valuation subring of `modularFunctionFieldC k 1` which contains the image of $k$, is not the whole field, and is a principal ideal ring; write $v.\mathrm{ord}$ for the associated integer-valued order function, minus the logarithm of the valuation attached to the height-one prime of that valuation ring. The hypothesis is that the element `jqModC k` of `modularFunctionFieldC k 1` has strictly negative order at $v$. The conclusion is that $v$ is the image, under the bijection `charLGeomPlaceEquiv k` of places induced by the $k$-algebra isomorphism $k(t)\xrightarrow{\sim}$ `modularFunctionFieldC k 1` carrying $t$ to `jqModC k`, of the place at infinity `RationalFunctionField.placeInfty k` of the rational function field, given by the valuation subring of `RatFunc.inftyValuation k`.
--
--   This is the cusp clause of the classification of places of the $j$-line over an arbitrary field: a place at which the modular coordinate has a pole is the unique place at infinity. It is used in the analysis of level-one place specialisations, where it pins the specialisation of places without integral centre to the cusp $\tilde\jmath=\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] {v : Place k ↥(modularFunctionFieldC k 1)}
    (h : v.ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)) < 0) :
    v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by sorry
