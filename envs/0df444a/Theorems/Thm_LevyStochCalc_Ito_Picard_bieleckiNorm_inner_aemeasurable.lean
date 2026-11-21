-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_inner_aemeasurable
-- name    : LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:28:32.352985+00:00
-- url     : https://prove2.me/theorems/9da69b7f-47a7-458e-968d-d4eb6e8c5ed8
-- title:
--   bieleckiNorm inner aemeasurable
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable` is extracted from `LevyStochCalc.Ito.PicardSpaceBieleckiQuotient`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Bielecki pseudo-emetric space and its separation quotient

The type synonym `SBoundedProcess.WithBielecki` carries the Bielecki β-weighted pseudo-edist,
keeping it apart from the discrete metric on `SBoundedProcess` itself. Its triangle inequality
comes from subadditivity of the Bielecki norm applied to the pointwise identity
`X - Z = (X - Y) + (Y - Z)`, whose measurability side conditions follow from slice
measurability of the inner integrand `ω ↦ (∑ i, ‖X t ω i‖₊²)^(1/2)`. The resulting
`PseudoEMetricSpace` has a separation quotient `SBoundedProcess.AEQuot`, an `EMetricSpace`
identifying processes that agree P-a.s. at each fixed `t`; the constant-zero process inhabits
both the synonym and the quotient. A closing note contrasts this weighted sup-of-`L²` norm
with the `S²` norm and records the role of the `IsRegular` hypothesis in well-posedness.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Type-synonym carrying the Bielecki pseudo-edist instance

To avoid clashing with the existing discrete `MetricSpace` instance in
`LevyStochCalc.Ito.PicardSpaceDiscrete`, we equip a **type synonym** with the Bielecki
pseudo-edist instance. Downstream callers wanting the literature metric
write `SBoundedProcess.WithBielecki n P ℱ T β` explicitly. -/

namespace SBoundedProcess.WithBielecki

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}

end SBoundedProcess.WithBielecki

/-! ### EDist + PseudoEMetricSpace instances on `WithBielecki`

The instance is on `WithBielecki`, not on `SBoundedProcess` directly,
so the existing discrete-metric instance in `LevyStochCalc.Ito.PicardSpaceDiscrete` is
preserved. -/

/-! ### Measurability of the inner Bielecki integrand

The `PseudoEMetricSpace` instance on `SBoundedProcess.WithBielecki n P ℱ T β` needs the three
edist axioms: `bieleckiEDist_self` and `bieleckiEDist_comm`, and the triangle inequality, which
applies `bieleckiNorm_add_le` to `Y₁ = X - Y`, `Y₂ = Y - Z` and identifies
`(X - Y) + (Y - Z) = X - Z` pointwise. `bieleckiNorm_add_le` asks for the per-`t`
a.e.-measurability of `ω ↦ (∑ i, ‖X.X t ω i‖₊²)^(1/2)`, which
`bieleckiNorm_inner_aemeasurable` derives from the joint measurability
`LevyStochCalc.Ito.Picard.SBoundedProcess.measurable_path` of the path map. -/

theorem _root_.LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X)) (t : ℝ) :
    AEMeasurable
      (fun ω => (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P := by sorry
