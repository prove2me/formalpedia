-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_gradient_K_representation
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:15:06.349714+00:00
-- url     : https://prove2.me/theorems/355611df-fae1-4cb1-a641-e37816d69b5a
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation` of [lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff Topology InnerProductSpace Laplacian`, `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace Laplacian Topology`, `open DiskH10 PlaneGreen`):
--
--   ```lean
--   theorem gradient_K_representation (hΩ : AdmissibleDomain Ω)
--       {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
--       (hne : ∃ x ∈ Ω, u x ≠ 0) (x : disk) (e : Plane) :
--       let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
--       inner ℝ (gradient u (c.F x)) e =
--         ∫ s, fullBoundaryK c.densityBound_ne_top
--           (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) x s *
--           inner ℝ (closedGradient Ω u (c.F s)) e ∂boundaryMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.closedGradient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.PlaneGreen.Boundary`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.firstPositiveNeumannValue_pos_of_eigenfunction`, `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure` and `OAI.StrictHotSpots.PlaneGreen.fullBoundaryK` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential_finite` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace`, `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section OriginalGradientKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Laplacian
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Laplacian Topology
namespace StrictHotSpots

namespace Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

theorem gradient_K_representation (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) (x : disk) (e : Plane) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    inner ℝ (gradient u (c.F x)) e =
      ∫ s, fullBoundaryK c.densityBound_ne_top
        (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) x s *
        inner ℝ (closedGradient Ω u (c.F s)) e ∂boundaryMeasure := by
  sorry

end Conformal.ClosedDiskChart
end StrictHotSpots
end
end
end OriginalGradientKernel

end OAI
end
