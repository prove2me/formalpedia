-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_mul_tendsto
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_mul_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:16:52.21993+00:00
-- url     : https://prove2.me/theorems/0c7645ae-5d2b-4a7d-8965-14e062da281d
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_mul_tendsto: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_mul_tendsto` of [lean/OAI/Analysis/HotSpots/HotSpots/ClosedSolution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/ClosedSolution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace ENNReal NNReal Topology`, `open DiskH10 PlaneGreen Hodge`):
--
--   ```lean
--   lemma scalarSolution_mul_tendsto {w b : Plane → ℝ}
--       (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0} (hb : LipschitzWith B b) :
--       Tendsto (fun n => c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ
--         ((ambientSmooth_smooth (planeApproxBump n) hb).contDiffOn.mul hw)) atTop
--         (𝓝 (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
--           (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.H10.grad`, `OAI.StrictHotSpots.H10.value` and `OAI.StrictHotSpots.HasH1Gradient.toH1` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.ambientSmooth`, `OAI.StrictHotSpots.ambientSmooth_smooth`, `OAI.StrictHotSpots.planeApproxBump` and `OAI.StrictHotSpots.smooth_closure_H1` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.H1.lipschitzMul`, `OAI.StrictHotSpots.PhysicalHelmholtz.extension` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/ClosedSolution.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_mul_tendsto)

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

lemma scalarSolution_mul_tendsto {w b : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0} (hb : LipschitzWith B b) :
    Tendsto (fun n => c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ
      ((ambientSmooth_smooth (planeApproxBump n) hb).contDiffOn.mul hw)) atTop
      (𝓝 (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
        (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1))) := by
  sorry

end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalMultiplierClosed

end OAI
end
