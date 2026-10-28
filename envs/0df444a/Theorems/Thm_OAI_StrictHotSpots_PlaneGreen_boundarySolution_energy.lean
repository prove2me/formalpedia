-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_boundarySolution_energy
-- name    : OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:12:30.004286+00:00
-- url     : https://prove2.me/theorems/95828915-f108-4138-b66c-b48e84fcfe00
-- title:
--   OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy` of [lean/OAI/Analysis/HotSpots/HotSpots/GreenSolution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/GreenSolution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.PlaneGreen`, with `open Set MeasureTheory Filter Metric`, `open scoped Topology ContDiff InnerProductSpace ENNReal NNReal`, `open DiskH10`):
--
--   ```lean
--   theorem boundarySolution_energy (hT : ‖weightedIntegralOperator hC hν‖ < 1)
--       (f g : C(Boundary,ℝ)) {A B : ℝ≥0} (hf : LipschitzWith A f) (hg : LipschitzWith B g) :
--       inner ℝ (H1.grad (boundarySolution hC hν f hf)) (H1.grad (boundarySolution hC hν g hg)) -
--         inner ℝ (SubcriticalExtension.observe hC hν (boundarySolution hC hν f hf))
--           (SubcriticalExtension.observe hC hν (boundarySolution hC hν g hg)) =
--         (1/2:ℝ)*(∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
--           inner ℝ (f z.1-f z.2) (g z.1-g z.2) ∂boundaryMeasure.prod boundaryMeasure) -
--         (∫ z : Boundary × Boundary, fullBoundaryR hC hν z.1 z.2 * f z.1 * g z.2
--           ∂boundaryMeasure.prod boundaryMeasure)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.H1.grad` and `OAI.StrictHotSpots.PlaneGreen.Boundary` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.PlaneGreen.boundarySolution` and `OAI.StrictHotSpots.SubcriticalExtension.observe` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.PlaneGreen.boundaryInteraction`, `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure`, `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR` and `OAI.StrictHotSpots.PlaneGreen.weightedIntegralOperator` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/GreenSolution.lean (declaration OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
import Definitions.Def_OAIQ3Ho003

section

attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section BoundaryScalarEnergy

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)

theorem boundarySolution_energy (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f g : C(Boundary,ℝ)) {A B : ℝ≥0} (hf : LipschitzWith A f) (hg : LipschitzWith B g) :
    inner ℝ (H1.grad (boundarySolution hC hν f hf)) (H1.grad (boundarySolution hC hν g hg)) -
      inner ℝ (SubcriticalExtension.observe hC hν (boundarySolution hC hν f hf))
        (SubcriticalExtension.observe hC hν (boundarySolution hC hν g hg)) =
      (1/2:ℝ)*(∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
        inner ℝ (f z.1-f z.2) (g z.1-g z.2) ∂boundaryMeasure.prod boundaryMeasure) -
      (∫ z : Boundary × Boundary, fullBoundaryR hC hν z.1 z.2 * f z.1 * g z.2
        ∂boundaryMeasure.prod boundaryMeasure) := by
  sorry

end StrictHotSpots.PlaneGreen
end
end BoundaryScalarEnergy

end OAI
end
