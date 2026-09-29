-- Prove2me | Theorems.Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase
-- name    : ModularCurve.tateCurve_curve_X_pow_eq_tateBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5928e538-e40b-571c-8c64-a69f77381c47
-- title:
--   Analytic Tate curve at q=tᵖ equals the formal Tate base
-- statement:
--   Let $F$ be a field and let $p$ be a nonzero natural number. Give the Laurent series field `LaurentSeries F` its $X$-adic structure as a nontrivially normed ultrametric field, and write $t =$ `HahnSeries.single (1 : ℤ) (1 : F)` for the uniformiser. The assertion is an equality of Weierstrass curves over `LaurentSeries F`. On the left stands [`TateCurve.curve`](def/TateCurve_QSeries.html#L185) evaluated at the parameter $t^p$, that is the curve $\langle 1, 0, 0,$ `a₄` $(t^p),$ `a₆` $(t^p)\rangle$, whose fourth and sixth coefficients are the values at $t^p$ of the analytic $q$-series `a₄` and `a₆` attached to a parameter in an ultrametric field. On the right stands [`ModularCurve.tateBase F p`](def/ModularCurve_TateSlots.html#L46), defined as the image of [`ModularCurve.tateLaurent F`](def/ModularCurve_TateFormal.html#L86) — itself the base change of the integral Weierstrass curve `tatePowerSeries` along `laurentOfInt F` — under the ring homomorphism [`ModularCurve.qExpand F p`](def/ModularCurve_X0.html#L25), which multiplies all Hahn series exponents by $p$, i.e. substitutes $q \mapsto q^p$. Equality of the two curves means equality of all five coefficients $a_1, a_2, a_3, a_4, a_6$; the first three are $1, 0, 0$ on both sides.
--
--   This identifies the analytically defined Tate curve over $F((t))$, with its convergent Lambert-series coefficients, with the integral divisor-sum Tate model read in the parameter $q = t^p$, the classical $q$-expansion form of the Tate parametrisation. It is the bridge used by the computations of division-polynomial values at the toric and non-toric points of [`ModularCurve.tateBase`](def/ModularCurve_TateSlots.html#L46).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase.lean

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_curve_X_pow_eq_tateBase (F : Type*) [Field F] (p : ℕ) [NeZero p] :
    TateCurve.curve ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) = ModularCurve.tateBase F p := by sorry
