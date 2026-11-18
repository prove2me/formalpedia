-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedLocalOnlineActionsWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:00.020488+00:00
-- url     : https://prove2.me/theorems/4f224823-4a84-4b09-b82a-237031b45411
-- title:
--   OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedLocalOnlineWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedLocalOnlineWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem preparedLocalOnlineActionsWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
--       (parent : TargetInterval source.length) (N P F exponent H B E S : ℕ)
--       (hPpos : 0 < P) (hMpos : 0 < M)
--       (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
--       (child initial : Fin M → TargetInterval target.length → BinaryFraction)
--       (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
--       (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
--       (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
--       (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
--       (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
--       (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
--       (hInteger : ∀ b r, Nat.size (integer b r) ≤ B)
--       (htau : tau.width ≤ B) (ha : a.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
--       (hparent : ∀ r, (parentInitial r).width ≤ B)
--       (hchild : ∀ i q, (child i q).width ≤ B) (hinitial : ∀ i q, (initial i q).width ≤ B)
--       (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
--       (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
--       (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
--         (table s (i, q)).value ≤ (initial i q).value)
--       (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
--       (hBS : 3 * (B + 4) + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
--       (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
--       (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
--       (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hPpos tau a eta kappa
--         parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineBitBudget M P B S
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork` and `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction` and `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRefinement_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedLocalOnlineWork.lean (declaration OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem preparedLocalOnlineActionsWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B E S : ℕ)
    (hPpos : 0 < P) (hMpos : 0 < M)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : ∀ b r, Nat.size (integer b r) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hparent : ∀ r, (parentInitial r).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * (B + 4) + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hPpos tau a eta kappa
      parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineBitBudget M P B S := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
