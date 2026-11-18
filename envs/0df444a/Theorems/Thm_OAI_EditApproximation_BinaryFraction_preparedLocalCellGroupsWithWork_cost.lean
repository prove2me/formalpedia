-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedLocalCellGroupsWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:50.285367+00:00
-- url     : https://prove2.me/theorems/15c80ecb-48e4-4356-b4ec-c87110b2910b
-- title:
--   OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedLocalGroupWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedLocalGroupWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem preparedLocalCellGroupsWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
--       (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
--       (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
--       (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
--       (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
--       (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
--       (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
--       (hQ : Nat.size Q + 2 ≤ B) (hP : Nat.size P ≤ B)
--       (hF : Nat.size F + 2 ≤ B) (he : exponent + 1 ≤ B) (hes : eM + eF + 7 ≤ B)
--       (htau : tau.width ≤ B) (ha : a.width ≤ B)
--       (hparent : ∀ q, (parentInitial q).width ≤ B)
--       (hchild : ∀ i q, (child i q).width ≤ B)
--       (hinitial : ∀ i q, (initial i q).width ≤ B)
--       (hcurrent : ∀ i q, (current i q).width ≤ B)
--       (hnonneg : 0 ≤ (parentInitial query).value)
--       (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
--       (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF
--         hMdef hFdef hPpos tau a parentInitial child initial current draw query).2 ≤
--         preparedLocalGroupsBitBudget N M P F exponent eM eF B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork` and `OAI.EditApproximation.BinaryFraction.preparedLocalGroupsBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction` and `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.CellGroupDraws` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedLocalGroupWork.lean (declaration OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem preparedLocalCellGroupsWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hP : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (he : exponent + 1 ≤ B) (hes : eM + eF + 7 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hnonneg : 0 ≤ (parentInitial query).value)
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF
      hMdef hFdef hPpos tau a parentInitial child initial current draw query).2 ≤
      preparedLocalGroupsBitBudget N M P F exponent eM eF B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
