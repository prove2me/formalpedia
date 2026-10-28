-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_multipliedGradient_coordinate_difference
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:15:39.74623+00:00
-- url     : https://prove2.me/theorems/b34ff094-a55b-40d1-83f0-2e98e888f041
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference` of [lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace ENNReal NNReal`, `open DiskH10 PlaneGreen Hodge`):
--
--   ```lean
--   lemma multipliedGradient_coordinate_difference {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) (i : Fin 2) :
--       let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
--       H1.form (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb i)
--         (c.multipliedGradient hΩ hu hμ hb i)-
--       H1.form (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu i)
--         (c.multipliedGradient hΩ hu hμ (hb.mul hb) i) =
--       (1/2:ℝ)*∫ z : Boundary × Boundary,
--         (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
--         (b (c.F z.1)-b (c.F z.2))^2*
--         inner ℝ (fderivWithin ℝ u (closure Ω) (c.F z.1) (Hodge.e i))
--           (fderivWithin ℝ u (closure Ω) (c.F z.2) (Hodge.e i)) ∂boundaryMeasure.prod boundaryMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.PlaneGreen.Boundary`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.Hodge.e` and `OAI.StrictHotSpots.Hodge.eigenGradientField` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.H1.form`, `OAI.StrictHotSpots.PlaneGreen.boundaryInteraction`, `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure` and `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential_finite` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace`, `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proofs of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel` and `OAI_StrictHotSpots_Conformal_ClosedDiskChart_smooth_multiplier_kernel` of this split import it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section SmoothMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

lemma multipliedGradient_coordinate_difference {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) (i : Fin 2) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    H1.form (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb i)
      (c.multipliedGradient hΩ hu hμ hb i)-
    H1.form (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu i)
      (c.multipliedGradient hΩ hu hμ (hb.mul hb) i) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (fderivWithin ℝ u (closure Ω) (c.F z.1) (Hodge.e i))
        (fderivWithin ℝ u (closure Ω) (c.F z.2) (Hodge.e i)) ∂boundaryMeasure.prod boundaryMeasure := by
  sorry

end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothMultiplierKernel

end OAI
end
