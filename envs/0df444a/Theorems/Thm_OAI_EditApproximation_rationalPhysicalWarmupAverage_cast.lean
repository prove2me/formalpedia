-- Prove2me | Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmupAverage_cast
-- name    : OAI.EditApproximation.rationalPhysicalWarmupAverage_cast
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:37.312476+00:00
-- url     : https://prove2.me/theorems/8957943b-46cb-401d-91c0-a994b8553906
-- title:
--   OAI.EditApproximation.rationalPhysicalWarmupAverage_cast: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.rationalPhysicalWarmupAverage_cast` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRationalWarmup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRationalWarmup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--   theorem rationalPhysicalWarmupAverage_cast {α : Type*} {M J : ℕ} (source target : List α)
--       (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
--       (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
--       (T : ℕ) (state : PhysicalEntry M J target.length) :
--       (rationalPhysicalWarmupAverage source target P L initial representatives T state : ℝ) =
--         physicalWarmupAverage source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives T state
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.rationalPhysicalWarmupAverage` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalWarmupAverage` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.PhysicalNode` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.stageComparisonCharges_local`, `OAI.EditApproximation.stageWarmup_invariants` and `OAI.EditApproximation.subtreeComparisonCharges_local` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalRationalWarmup.lean (declaration OAI.EditApproximation.rationalPhysicalWarmupAverage_cast)

import Mathlib
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

theorem rationalPhysicalWarmupAverage_cast {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalWarmupAverage source target P L initial representatives T state : ℝ) =
      physicalWarmupAverage source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives T state := by
  sorry

end EditApproximation

end OAI
end
