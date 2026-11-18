-- Prove2me | Theorems.Thm_OAI_EditApproximation_stageComparisonCharges_local
-- name    : OAI.EditApproximation.stageComparisonCharges_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:06.28972+00:00
-- url     : https://prove2.me/theorems/8e19698d-97cd-4f30-87fa-0311f00f62bd
-- title:
--   OAI.EditApproximation.stageComparisonCharges_local: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.stageComparisonCharges_local` of [lean/OAI/Combinatorics/EditApproximation/Refinement/StageComparisonCharges.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/StageComparisonCharges.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--    theorem stageComparisonCharges_local (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
--       (d : Fin J) (path : TreeLayer M d.val) :
--       let charges := stageComparisonCharges source target hM U N P F A hP T rootQ d path
--       let R := mass d.val path - ∑ i : Fin M, mass (d.val + 1) (path, i)
--       let E := (∑ i : Fin M, energy (d.val + 1) (path, i)) - energy d.val path
--       let movement := comparisonMovement source target P (frontier d.val path)
--       let cost := comparisonActiveCost source target (frontier d.val path)
--       0 ≤ charges.1 ∧ 0 ≤ charges.2 ∧
--         R + charges.2 ≤ (128 * (F : ℝ)) * movement + (2 * F / (T : ℝ)) * cost ∧
--         charges.1 ≤ E + 3 * movement + 2 * max (-R) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.comparisonActiveCost`, `OAI.EditApproximation.comparisonFrontier` and `OAI.EditApproximation.comparisonMovement` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.stageComparisonCharges`, `OAI.EditApproximation.stageComparisonEnergy` and `OAI.EditApproximation.stageComparisonMass` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode` and `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.sourceIntervalAt` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.physicalComparisonBadRegret_bound` and `OAI.EditApproximation.stageComparisonCharges_total` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/StageComparisonCharges.lean (declaration OAI.EditApproximation.stageComparisonCharges_local)

import Mathlib
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

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

local notation "mass" => stageComparisonMass source target hM U N P F A hP T rootQ
local notation "energy" => stageComparisonEnergy source target hM U N P F A hP T rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem stageComparisonCharges_local (hscale : 2 * (refinementFactor A F : ℝ) ≤ P)
    (d : Fin J) (path : TreeLayer M d.val) :
    let charges := stageComparisonCharges source target hM U N P F A hP T rootQ d path
    let R := mass d.val path - ∑ i : Fin M, mass (d.val + 1) (path, i)
    let E := (∑ i : Fin M, energy (d.val + 1) (path, i)) - energy d.val path
    let movement := comparisonMovement source target P (frontier d.val path)
    let cost := comparisonActiveCost source target (frontier d.val path)
    0 ≤ charges.1 ∧ 0 ≤ charges.2 ∧
      R + charges.2 ≤ (128 * (F : ℝ)) * movement + (2 * F / (T : ℝ)) * cost ∧
      charges.1 ≤ E + 3 * movement + 2 * max (-R) 0 := by
  sorry

end Stage

end EditApproximation

end OAI
end
