-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_querySharedCellInputsWithWork_value
-- name    : OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:51.04403+00:00
-- url     : https://prove2.me/theorems/619aa6b7-4336-4579-98e3-08ee47feb16b
-- title:
--   OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value` of [lean/OAI/Combinatorics/EditApproximation/Queries/QuerySharedInputs.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QuerySharedInputs.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem querySharedCellInputsWithWork_value {α : Type*} (source target : List α)
--       (M F Q eM eb eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
--       (parent : TargetInterval source.length) (exponent : ℕ) (cell : ℕ × ℕ)
--       (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
--         Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ) :
--       (querySharedCellInputsWithWork (ny := target.length) M F Q eM eb eF hM hF parent exponent cell draw).1.toFinset =
--         Finset.univ.biUnion (fun scale => groupCurrentInputCover source target parent (2 ^ eb) exponent Q cell
--           (groupDyadicScaleAt M (2 ^ eb) F scale) (fun sample => (draw scale sample).1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount` and `OAI.EditApproximation.instDecidableEqTargetInterval` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.groupCurrentInputCover` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.groupDyadicScaleAt` and `OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryRefinementGather_refines` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QuerySharedInputs.lean (declaration OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork_value)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace BinaryFraction

theorem querySharedCellInputsWithWork_value {α : Type*} (source target : List α)
    (M F Q eM eb eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (parent : TargetInterval source.length) (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ) :
    (querySharedCellInputsWithWork (ny := target.length) M F Q eM eb eF hM hF parent exponent cell draw).1.toFinset =
      Finset.univ.biUnion (fun scale => groupCurrentInputCover source target parent (2 ^ eb) exponent Q cell
        (groupDyadicScaleAt M (2 ^ eb) F scale) (fun sample => (draw scale sample).1)) := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
