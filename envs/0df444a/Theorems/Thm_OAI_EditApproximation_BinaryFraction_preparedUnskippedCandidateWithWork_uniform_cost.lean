-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedUnskippedCandidateWithWork_uniform_cost
-- name    : OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:25.611017+00:00
-- url     : https://prove2.me/theorems/7cafd030-0ee4-43b6-a4e8-ef5b756aca04
-- title:
--   OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedUnskippedWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedUnskippedWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem preparedUnskippedCandidateWithWork_uniform_cost {α : Type*} (source target : List α)
--       {M : ℕ} (parent : TargetInterval source.length) (b P e B : ℕ)
--       (hbpos : 0 < b) (hPpos : 0 < P) (tau F : BinaryFraction)
--       (child initial : Fin M → TargetInterval target.length → BinaryFraction)
--       (center : TargetInterval target.length)
--       (hnx : Nat.size source.length + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
--       (hM : Nat.size M ≤ B) (hb : Nat.size b + 2 ≤ B) (hP : Nat.size P ≤ B)
--       (he : e + 1 ≤ B) (htau : tau.width ≤ B) (hF : F.width ≤ B)
--       (hchild : ∀ i q, (child i q).width ≤ B)
--       (hinitial : ∀ i q, (initial i q).width ≤ B) :
--       (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau F
--         child initial center).2 ≤ preparedUnskippedBitBudget e b M P
--           ((40 * P + 2) ^ (2 * M)) ((40 * P + 2) ^ (2 * M)) B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.preparedUnskippedBitBudget` and `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost` and `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedUnskippedWork.lean (declaration OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem preparedUnskippedCandidateWithWork_uniform_cost {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (b P e B : ℕ)
    (hbpos : 0 < b) (hPpos : 0 < P) (tau F : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length)
    (hnx : Nat.size source.length + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b + 2 ≤ B) (hP : Nat.size P ≤ B)
    (he : e + 1 ≤ B) (htau : tau.width ≤ B) (hF : F.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B) :
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau F
      child initial center).2 ≤ preparedUnskippedBitBudget e b M P
        ((40 * P + 2) ^ (2 * M)) ((40 * P + 2) ^ (2 * M)) B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
