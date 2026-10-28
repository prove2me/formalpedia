-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitz_multiplier_kernel
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:15:18.584079+00:00
-- url     : https://prove2.me/theorems/de1bdf86-71ef-4bf0-b9aa-cbf9259f7b39
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel` of [lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace ENNReal NNReal Topology`, `open DiskH10 PlaneGreen Hodge`):
--
--   ```lean
--   theorem lipschitz_multiplier_kernel {b : Plane → ℝ} {B : ℝ≥0}
--       (hb : LipschitzWith B b) :
--       let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
--       vectorForm (firstPositiveNeumannValue Ω)
--         (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
--         (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) =
--       (1/2:ℝ)*∫ z : Boundary × Boundary,
--         (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
--         (b (c.F z.1)-b (c.F z.2))^2*
--         inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
--           ∂boundaryMeasure.prod boundaryMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.closedGradient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.H10.grad`, `OAI.StrictHotSpots.H10.value`, `OAI.StrictHotSpots.PlaneGreen.Boundary`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.PlaneGreen.boundaryInteraction`, `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure` and `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Hodge.vectorForm`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential_finite` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace`, `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

theorem lipschitz_multiplier_kernel {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
  sorry

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel

end OAI
end
