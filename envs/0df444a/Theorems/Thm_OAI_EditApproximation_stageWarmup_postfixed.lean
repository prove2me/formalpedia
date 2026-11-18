-- Prove2me | Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed
-- name    : OAI.EditApproximation.stageWarmup_postfixed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:44:00.696906+00:00
-- url     : https://prove2.me/theorems/5e437433-402f-4650-b9ff-6442b0a3f899
-- title:
--   OAI.EditApproximation.stageWarmup_postfixed: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.stageWarmup_postfixed` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRefinementInvariants.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRefinementInvariants.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem stageWarmup_postfixed {α : Type*} [DecidableEq α] {M J : ℕ}
--       (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
--       (N P F : ℕ) (A : ℚ) (T : ℕ) (state : PhysicalEntry M J target.length) :
--       rationalPhysicalBellman source target P (128 * F) (stageInitial source target U N P F A)
--           (stageRepresentatives source target U N P F A)
--           (stageWarmup source target U N P F A T) state ≤
--         stageWarmup source target U N P F A T state
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.rationalPhysicalBellman`, `OAI.EditApproximation.stageInitial` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.stageWarmup` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.localFinalProgramValue_eq`, `OAI.EditApproximation.localScheduledSeedNext_event`, `OAI.EditApproximation.physicalBand_prefix_expected_regret`, `OAI.EditApproximation.physicalNode_firstCrossing_regret`, `OAI.EditApproximation.physicalNode_generic_regret`, `OAI.EditApproximation.physicalRefinement_stage_bounds`, `OAI.EditApproximation.physical_tree_expected_excess` and `OAI.EditApproximation.subtree_expected_excess_of_good_nodes` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRefinementInvariants.lean (declaration OAI.EditApproximation.stageWarmup_postfixed)

import Mathlib
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

theorem stageWarmup_postfixed {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (state : PhysicalEntry M J target.length) :
    rationalPhysicalBellman source target P (128 * F) (stageInitial source target U N P F A)
        (stageRepresentatives source target U N P F A)
        (stageWarmup source target U N P F A T) state ≤
      stageWarmup source target U N P F A T state := by
  sorry

end EditApproximation

end OAI
end
