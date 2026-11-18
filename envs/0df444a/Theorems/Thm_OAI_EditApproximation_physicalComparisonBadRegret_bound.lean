-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalComparisonBadRegret_bound
-- name    : OAI.EditApproximation.physicalComparisonBadRegret_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:24.594931+00:00
-- url     : https://prove2.me/theorems/d279a6c1-8722-4e29-ae57-4b7b8e80bc9b
-- title:
--   OAI.EditApproximation.physicalComparisonBadRegret_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalComparisonBadRegret_bound` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalTreeGeneric.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalTreeGeneric.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--    theorem physicalComparisonBadRegret_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
--       (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
--       (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
--       (∑ v : (Σ d : Fin J, TreeLayer M d.val) with
--         comparisonActiveScale source target (frontier v.1.val v.2) <
--           ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1 ∨
--         comparisonActiveScale source target (frontier v.1.val v.2) <
--           ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2,
--         ∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t v.1 v.2) ≤
--         40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) *
--           comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalSelections` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.comparisonActiveScale`, `OAI.EditApproximation.comparisonFrontier` and `OAI.EditApproximation.comparisonStateCost` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalComparisonTreeRegret` and `OAI.EditApproximation.stageComparisonCharges` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.TreeLayer` and `OAI.EditApproximation.treeLayerFintype` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.sourceIntervalAt` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_expected_root_excess` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalTreeGeneric.lean (declaration OAI.EditApproximation.physicalComparisonBadRegret_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem physicalComparisonBadRegret_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val) with
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2,
      ∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t v.1 v.2) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) *
        comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  sorry

end Tree

end EditApproximation

end OAI
end
