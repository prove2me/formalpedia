-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
-- name    : ModularCurve.IgusaScheme.geometricallyConnected_toBase_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/e0e4fd06-a168-54eb-8b83-1dbc1c0e33eb
-- title:
--   Geometric connectedness over ℤ of the two-chart model of X₀(N)
-- statement:
--   Let $N$ be a natural number with `NeZero N`, i.e. $N \ne 0$. Let $F =$ `modularFunctionFieldFull N` be the subfield of the field of Laurent series over $\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the set of expansions `qExpand ℚ d jq` for the nonzero divisors $d$ of $N$, and let $j =$ `jFull N` be the element of $F$ given by the expansion `jq` of the modular invariant. Over the base ring $\mathbb{Z}$, form [`AlgebraicCurve.TwoChartIntegralModel ℤ F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout in schemes of the two morphisms `fFin` and `fInf` from `XMid` to the spectra of the chart algebras `chartAlg ℤ F {j}` and `chartAlg ℤ F {j⁻¹}` induced by the inclusions `inclFin` and `inclInf`, and let `toBase` be the morphism from this pushout to $\operatorname{Spec}\mathbb{Z}$ obtained by descending the two morphisms $\operatorname{Spec}$ of the structure maps $\mathbb{Z} \to$ `chartAlg ℤ F {j}` and $\mathbb{Z} \to$ `chartAlg ℤ F {j⁻¹}`. The assertion is that `toBase` is geometrically connected: every base change of it along a morphism $\operatorname{Spec} K \to \operatorname{Spec}\mathbb{Z}$ with $K$ a field has connected, in particular nonempty, underlying space. No restriction on the characteristic of $K$ relative to $N$ is imposed.
--
--   This is the geometric connectedness over $\operatorname{Spec}\mathbb{Z}$ of the two-chart integral model of $X_0(N)$, covering all fibres, including those at primes dividing $N$. It is used in the study of the Deligne–Rapoport model package, notably for the bijectivity of the map on sections under base change and for the existence of locally split pools.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.IgusaScheme.geometricallyConnected_toBase_int (N : ℕ) [NeZero N] :
    GeometricallyConnected
      (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N)) := by sorry
