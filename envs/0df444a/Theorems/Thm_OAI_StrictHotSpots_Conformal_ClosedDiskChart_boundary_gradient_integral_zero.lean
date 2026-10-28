-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_boundary_gradient_integral_zero
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:12:50.297622+00:00
-- url     : https://prove2.me/theorems/73bb94f1-8b99-4a3a-8641-21733461a072
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero` of [lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter Metric Function`, `open scoped ENNReal NNReal Topology InnerProductSpace`, `open PlaneGreen DiskH10`):
--
--   ```lean
--   lemma boundary_gradient_integral_zero (hΩ : AdmissibleDomain Ω)
--       {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
--       (p : disk) (hz : gradient u (c.F p) = 0) :
--       let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
--       (∫ s, fullBoundaryK c.densityBound_ne_top
--         (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s •
--         closedGradient Ω u (c.F s) ∂boundaryMeasure) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.closedGradient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.PlaneGreen.Boundary`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.firstPositiveNeumannValue_pos_of_eigenfunction`, `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure` and `OAI.StrictHotSpots.PlaneGreen.fullBoundaryK` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential_finite` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace`, `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section OriginalGradientVector

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
lemma boundary_gradient_integral_zero (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) (hz : gradient u (c.F p) = 0) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    (∫ s, fullBoundaryK c.densityBound_ne_top
      (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s •
      closedGradient Ω u (c.F s) ∂boundaryMeasure) = 0 := by
  sorry
end StrictHotSpots.Conformal.ClosedDiskChart
end
end OriginalGradientVector

end OAI
end
