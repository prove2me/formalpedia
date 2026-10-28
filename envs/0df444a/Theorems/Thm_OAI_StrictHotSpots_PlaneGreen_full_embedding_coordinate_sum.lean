-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_full_embedding_coordinate_sum
-- name    : OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:11:37.151991+00:00
-- url     : https://prove2.me/theorems/65f2ac4b-31df-4512-bc82-20bf3762ad8b
-- title:
--   OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum` of [lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.PlaneGreen`, with `open Set MeasureTheory Filter Metric Function`, `open scoped ENNReal NNReal Topology InnerProductSpace`, `open DiskH10`):
--
--   ```lean
--   theorem full_embedding_coordinate_sum {H E ι : Type*} [NormedAddCommGroup H]
--       [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
--       [Countable ι] (e : HilbertBasis ι ℝ H)
--       (p : disk) (hT : ‖weightedIntegralOperator hC hν‖ < 1) {b : Boundary → H}
--       (hb : Continuous b) (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel hC hν p s t)
--       {g : Boundary → E} (hg : Continuous g) :
--       HasSum (fun i => (1/2:ℝ)*∫ z : Boundary × Boundary,
--         fullBoundaryN hC hν z.1 z.2 * (inner ℝ (e i) (b z.1-b z.2))^2 *
--           inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)
--         ((1/2:ℝ)*‖∫ s, fullBoundaryK hC hν p s • g s ∂boundaryMeasure‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.DiskH10.disk` and `OAI.StrictHotSpots.PlaneGreen.Boundary` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.PlaneGreen.boundaryMeasure`, `OAI.StrictHotSpots.PlaneGreen.fullBoundaryK`, `OAI.StrictHotSpots.PlaneGreen.fullBoundaryN`, `OAI.StrictHotSpots.PlaneGreen.fullDistanceKernel` and `OAI.StrictHotSpots.PlaneGreen.weightedIntegralOperator` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean (declaration OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section HilbertKernelCoordinates

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

theorem full_embedding_coordinate_sum {H E ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Countable ι] (e : HilbertBasis ι ℝ H)
    (p : disk) (hT : ‖weightedIntegralOperator hC hν‖ < 1) {b : Boundary → H}
    (hb : Continuous b) (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel hC hν p s t)
    {g : Boundary → E} (hg : Continuous g) :
    HasSum (fun i => (1/2:ℝ)*∫ z : Boundary × Boundary,
      fullBoundaryN hC hν z.1 z.2 * (inner ℝ (e i) (b z.1-b z.2))^2 *
        inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)
      ((1/2:ℝ)*‖∫ s, fullBoundaryK hC hν p s • g s ∂boundaryMeasure‖^2) := by
  sorry

end StrictHotSpots.PlaneGreen
end
end HilbertKernelCoordinates

end OAI
end
