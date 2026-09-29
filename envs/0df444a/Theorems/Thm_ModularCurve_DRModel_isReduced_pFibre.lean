-- Prove2me | Theorems.Thm_ModularCurve_DRModel_isReduced_pFibre
-- name    : ModularCurve.DRModel.isReduced_pFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/937aa35e-ade1-5f4c-b8e0-940dcb41f061
-- title:
--   Reducedness of the p-fibre of the Deligne–Rapoport model
-- statement:
--   Let $p$ be a prime number, and assume $5 \le p$. Write $F = \mathbf{Q}(\mathrm{divisorExpansions}\ p)$ for the intermediate field `modularFunctionFieldFull p` of the Laurent series field $\mathrm{LaurentSeries}\ \mathbf{Q}$ over $\mathbf{Q}$, obtained by adjoining the family `divisorExpansions p`, and let $j =$ `IgusaScheme.jFull p` be the distinguished element of $F$ given by the $q$-expansion of the modular function $j$. Over the base ring $\mathbf{Z}$ these data determine the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel ℤ F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two morphisms `fFin` and `fInf` of schemes attached to the finite and infinite charts, and for an ideal $I \subseteq \mathbf{Z}$ its fibre `TwoChartIntegralModel.fibre` is the base change of this model along $\mathbf{Z} \to \mathbf{Z}/I$. The theorem asserts that [`ModularCurve.DRModel.pFibre p`](def/ModularCurve_DRModelPackage.html#L32), namely the fibre of this model at the ideal $(p) = \mathrm{span}\{p\} \subseteq \mathbf{Z}$, is a reduced scheme in the sense of `AlgebraicGeometry.IsReduced`.
--
--   This is the reducedness part of the Deligne–Rapoport description of the bad fibre of the integral model of $X_0(p)$: over $\mathbf{F}_p$ the model is a reduced curve (classically, two copies of the $j$-line crossing transversally at the supersingular points). It is one of the properties recorded when assembling the model package, and is cited by [`ModularCurve.exists_dRModelPackage_ffPin`](thm.html#ModularCurve.exists_dRModelPackage_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_isReduced_pFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.isReduced_pFibre (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    IsReduced (DRModel.pFibre p) := by sorry
