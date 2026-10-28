-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_fullBoundaryR_symm
-- name    : OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:10:53.849994+00:00
-- url     : https://prove2.me/theorems/6cc13507-60e3-4b32-bcca-479ec5895f75
-- title:
--   OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm` of [lean/OAI/Analysis/HotSpots/HotSpots/BoundaryEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/BoundaryEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.PlaneGreen`, with `open MeasureTheory Filter Set Metric`, `open scoped ENNReal Topology InnerProductSpace`, `open DiskH10`):
--
--   ```lean
--   lemma fullBoundaryR_symm (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
--       fullBoundaryR hC hν s t = fullBoundaryR hC hν t s
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.DiskH10.disk` and `OAI.StrictHotSpots.PlaneGreen.Boundary` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR` and `OAI.StrictHotSpots.PlaneGreen.weightedIntegralOperator` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/BoundaryEnergy.lean (declaration OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

section

attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryRPropertiesScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryR_symm (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    fullBoundaryR hC hν s t = fullBoundaryR hC hν t s := by
  sorry

end StrictHotSpots.PlaneGreen
end BoundaryRPropertiesScalarSupportLayer

end
end LipschitzBoundaryScalarSupport

end OAI
end
