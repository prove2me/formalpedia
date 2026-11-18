-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalRefinement_stage_bounds
-- name    : OAI.EditApproximation.physicalRefinement_stage_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:50.811457+00:00
-- url     : https://prove2.me/theorems/76c13005-53f0-4e4a-88d4-30dd58feb579
-- title:
--   OAI.EditApproximation.physicalRefinement_stage_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalRefinement_stage_bounds` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRefinementInvariants.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRefinementInvariants.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem physicalRefinement_stage_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
--       (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
--       (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
--       (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
--       (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
--         (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
--       (T : ℕ) (hT : 0 < T) (delta : ℚ)
--       (choices : PhysicalSelections M J source.length target.length P
--         (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
--       (t : ℕ) (q : TargetInterval target.length) :
--       physicalLower source target (refinementFactor A F : ℝ) (node, q) ≤
--           (physicalRefinement source target U N P F A T delta choices node t q : ℝ) ∧
--         physicalRefinement source target U N P F A T delta choices node t q ≤
--           stageWarmup source target U N P F A T (node, q) ∧
--         stageWarmup source target U N P F A T (node, q) ≤ stageWarmupMass source target U N P F A T (node, q) ∧
--         stageWarmupMass source target U N P F A T (node, q) ≤ stageInitial source target U N P F A (node, q) ∧
--         stageInitial source target U N P F A (node, q) ≤
--           2 * F * stateEditCost (physicalSource source node) target q
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalSelections`, `OAI.EditApproximation.stageInitial` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.physicalLower` and `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.physicalRefinement`, `OAI.EditApproximation.stageWarmup` and `OAI.EditApproximation.stageWarmupMass` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSource` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.localFinalProgram_accuracy`, `OAI.EditApproximation.physicalBand_prefix_expected_regret`, `OAI.EditApproximation.physicalMedianUpdate_lower`, `OAI.EditApproximation.physicalNode_firstCrossing_regret`, `OAI.EditApproximation.physicalRefinement_zero_cost` and `OAI.EditApproximation.physical_conditional_node_regret` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRefinementInvariants.lean (declaration OAI.EditApproximation.physicalRefinement_stage_bounds)

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem physicalRefinement_stage_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    physicalLower source target (refinementFactor A F : ℝ) (node, q) ≤
        (physicalRefinement source target U N P F A T delta choices node t q : ℝ) ∧
      physicalRefinement source target U N P F A T delta choices node t q ≤
        stageWarmup source target U N P F A T (node, q) ∧
      stageWarmup source target U N P F A T (node, q) ≤ stageWarmupMass source target U N P F A T (node, q) ∧
      stageWarmupMass source target U N P F A T (node, q) ≤ stageInitial source target U N P F A (node, q) ∧
      stageInitial source target U N P F A (node, q) ≤
        2 * F * stateEditCost (physicalSource source node) target q := by
  sorry

end EditApproximation

end OAI
end
