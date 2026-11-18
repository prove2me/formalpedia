-- Prove2me | Theorems.Thm_OAI_EditApproximation_physical_tree_expected_excess
-- name    : OAI.EditApproximation.physical_tree_expected_excess
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:48.979046+00:00
-- url     : https://prove2.me/theorems/97c50d47-6efe-496c-bcab-e1df1691ea21
-- title:
--   OAI.EditApproximation.physical_tree_expected_excess: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physical_tree_expected_excess` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalTreeExpectation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalTreeExpectation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--    theorem physical_tree_expected_excess (S : ℕ) (hS : 0 < S)
--       (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
--       (budget : (d : ℕ) → TreeLayer M d → ℝ)
--       (hnode : ∀ d < J, ∀ path : TreeLayer M d,
--         (∫ ω, (∑ t ∈ range S,
--           (lifted ω (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
--             ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path) :
--       (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) ≤
--         ((8 * (M : ℝ) + 512 * F) * J / P) * D +
--           (∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path) / S
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalSelections` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.comparisonFrontier`, `OAI.EditApproximation.comparisonMovement` and `OAI.EditApproximation.physicalRefinement` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalClippedLift` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.TreeLayer` and `OAI.EditApproximation.treeLayerFintype` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.sourceIntervalAt` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_expected_root_excess` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalTreeExpectation.lean (declaration OAI.EditApproximation.physical_tree_expected_excess)

import Mathlib
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

open Finset MeasureTheory ProbabilityTheory

section Expectation

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "D" => (stateEditCost source target rootQ : ℝ)
local notation "root" => (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J)
local notation "lifted" => fun ω => physicalClippedLift source target hM U N P F A hP T delta (choices ω) rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem physical_tree_expected_excess (S : ℕ) (hS : 0 < S)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (budget : (d : ℕ) → TreeLayer M d → ℝ)
    (hnode : ∀ d < J, ∀ path : TreeLayer M d,
      (∫ ω, (∑ t ∈ range S,
        (lifted ω (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * J / P) * D +
        (∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path) / S := by
  sorry

end Expectation

end EditApproximation

end OAI
end
