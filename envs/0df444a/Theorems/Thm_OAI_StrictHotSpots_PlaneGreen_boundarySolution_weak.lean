-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_boundarySolution_weak
-- name    : OAI.StrictHotSpots.PlaneGreen.boundarySolution_weak
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:18:01.633064+00:00
-- url     : https://prove2.me/theorems/ff1b4e57-6c58-4574-a530-35b596946aaa
-- title:
--   OAI.StrictHotSpots.PlaneGreen.boundarySolution_weak: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.PlaneGreen.boundarySolution_weak` of [lean/OAI/Analysis/HotSpots/HotSpots/GreenSolution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/GreenSolution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.PlaneGreen`, with `open Set MeasureTheory Filter Metric`, `open scoped Topology ContDiff InnerProductSpace ENNReal NNReal`, `open DiskH10`):
--
--   ```lean
--   lemma boundarySolution_weak (hT : ‖weightedIntegralOperator hC hν‖ < 1)
--       (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
--       SubcriticalExtension.WeakPotential diskOpen hC hν (boundarySolution hC hν f hf)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.PlaneGreen.Boundary` and `OAI.StrictHotSpots.PlaneGreen.diskOpen` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.PlaneGreen.boundarySolution` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.PlaneGreen.weightedIntegralOperator` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.SubcriticalExtension.WeakPotential` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proofs of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_weak` and `OAI.StrictHotSpots.PlaneGreen.value_K_of_trace` of this split import it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/GreenSolution.lean (declaration OAI.StrictHotSpots.PlaneGreen.boundarySolution_weak)

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

section BoundaryScalarEnergy

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)

omit [IsFiniteMeasure ν] in
lemma boundarySolution_weak (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    SubcriticalExtension.WeakPotential diskOpen hC hν (boundarySolution hC hν f hf) := by
  sorry

end StrictHotSpots.PlaneGreen
end
end BoundaryScalarEnergy

end OAI
end
