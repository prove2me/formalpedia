-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_full_boundary_hilbert_embedding
-- name    : OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:11:50.645994+00:00
-- url     : https://prove2.me/theorems/b2a2d0c0-c98d-42e4-b96d-4b05db259459
-- title:
--   OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding` of [lean/OAI/Analysis/HotSpots/HotSpots/KernelLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/KernelLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.PlaneGreen`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology InnerProductSpace`, `open DiskH10`):
--
--   ```lean
--   theorem full_boundary_hilbert_embedding {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
--       (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
--         d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk) :
--       ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
--         (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H) (b : Boundary → H) (L : ℝ≥0),
--         Function.Injective b ∧ LipschitzWith L b ∧
--           ∀ s t, ‖b s - b t‖ ^ 2 = fullDistanceKernel hC hν p s t
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.H10.grad`, `OAI.StrictHotSpots.PlaneGreen.Boundary` and `OAI.StrictHotSpots.PlaneGreen.diskOpen` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.H10.weightedValue` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.PlaneGreen.fullDistanceKernel` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/KernelLimit.lean (declaration OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
import Definitions.Def_OAIQ3Ho003

section

attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section FullBoundaryEmbeddingLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

theorem full_boundary_hilbert_embedding {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H) (b : Boundary → H) (L : ℝ≥0),
      Function.Injective b ∧ LipschitzWith L b ∧
        ∀ s t, ‖b s - b t‖ ^ 2 = fullDistanceKernel hC hν p s t := by
  sorry

end StrictHotSpots.PlaneGreen
end
end FullBoundaryEmbeddingLayer
end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end
