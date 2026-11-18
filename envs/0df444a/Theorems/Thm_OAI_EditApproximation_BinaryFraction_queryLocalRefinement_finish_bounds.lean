-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryLocalRefinement_finish_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:27:24.045284+00:00
-- url     : https://prove2.me/theorems/1225ae87-9ca8-466f-a1cc-1cf57e8ae92a
-- title:
--   OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalFinishCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalFinishCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryLocalRefinement_finish_bounds (B Rp earlierCount : ℕ)
--       (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
--       (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
--       (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
--       (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
--       (hpn : 0 ≤ (parentInitial q).1.value)
--       (hew : ∀ w ∈ earlierWords, w.width ≤ B) (hcw : ∀ w ∈ currentWords, w.width ≤ B)
--       (het : ∀ key ∈ earlierKeys, Nat.size key.2.1 ≤ B) (hel : earlierKeys.length ≤ earlierCount) :
--       let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
--         tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q).1
--       let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
--         parentInitial child initial R hc hi t integer earlierKeys earlierWords q).1
--       let keys := (queryNeededInputsWithWork groups online).1
--       let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
--       let lookup := queryFinishReadBudget M B Rp earlierCount G (B + 1)
--       (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
--         groups online keys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
--       (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
--         groups online keys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B lookup G (B + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.preparedKernelWordBudget`, `OAI.EditApproximation.BinaryFraction.queryFinishReadBudget`, `OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork`, `OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork` and `OAI.EditApproximation.BinaryFraction.queryRefinementFinishBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction` and `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.queryNeededInputsWithWork` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.CountedCellGroupDraws` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.queryChargedFamilyTable_semantic_width` and `OAI.EditApproximation.queryLocalRefinement_work_bound` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalFinishCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Finish
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) (earlierWords : List BinaryFraction)
  (sharedKeys : List (Fin M × TargetInterval target.length)) (sharedWords currentWords : List BinaryFraction)
  (q : TargetInterval target.length)

theorem queryLocalRefinement_finish_bounds (B Rp earlierCount : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ w ∈ earlierWords, w.width ≤ B) (hcw : ∀ w ∈ currentWords, w.width ≤ B)
    (het : ∀ key ∈ earlierKeys, Nat.size key.2.1 ≤ B) (hel : earlierKeys.length ≤ earlierCount) :
    let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q).1
    let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer earlierKeys earlierWords q).1
    let keys := (queryNeededInputsWithWork groups online).1
    let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
    let lookup := queryFinishReadBudget M B Rp earlierCount G (B + 1)
    (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
      groups online keys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
    (queryRefinementFinishWithWork parent N P F a delta parentInitial t earlierKeys earlierWords
      groups online keys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B lookup G (B + 1) := by
  sorry

end Finish
end EditApproximation.BinaryFraction

end OAI
end
