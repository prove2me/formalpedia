-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_closed_ae
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_closed_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:16:58.263986+00:00
-- url     : https://prove2.me/theorems/654ac956-29a4-400d-a941-3c1bf3fa36c4
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_closed_ae: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_closed_ae` of [lean/OAI/Analysis/HotSpots/HotSpots/ClosedSolution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/ClosedSolution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace ENNReal NNReal Topology`, `open DiskH10 PlaneGreen Hodge`):
--
--   ```lean
--   lemma scalarSolution_closed_ae {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
--       {M : ℝ} (hM : ∀ s : Boundary, ‖w (c.F s)‖ ≤ M) :
--       let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
--       (H1.value (c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw) : Plane → ℝ)
--         =ᵐ[volume.restrict Ω]
--         (boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le)
--           (c.datumTrace w hw.continuousOn) hM) ∘ c.G
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.H1.value`, `OAI.StrictHotSpots.PlaneGreen.Boundary`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.datumTrace`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.PlaneGreen.boundaryClosedSolution` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential_finite` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/ClosedSolution.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_closed_ae)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalMultiplierClosed

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma scalarSolution_closed_ae {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    {M : ℝ} (hM : ∀ s : Boundary, ‖w (c.F s)‖ ≤ M) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    (H1.value (c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw) : Plane → ℝ)
      =ᵐ[volume.restrict Ω]
      (boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le)
        (c.datumTrace w hw.continuousOn) hM) ∘ c.G := by
  sorry

end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalMultiplierClosed

end OAI
end
