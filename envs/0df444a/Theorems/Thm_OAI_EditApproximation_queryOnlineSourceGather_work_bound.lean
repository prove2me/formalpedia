-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryOnlineSourceGather_work_bound
-- name    : OAI.EditApproximation.queryOnlineSourceGather_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:16.546474+00:00
-- url     : https://prove2.me/theorems/e199ed69-a939-42d0-ae84-2c4f06ba22b5
-- title:
--   OAI.EditApproximation.queryOnlineSourceGather_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryOnlineSourceGather_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QuerySourceGatherCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QuerySourceGatherCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryOnlineSourceGather_work_bound {ι β α : Type*} (source target : List α) {M : ℕ}
--       (parent : TargetInterval source.length) (N P F exponent H B Rp R W K : ℕ) (hP : 0 < P)
--       (tau a : BinaryFraction) (initial : TargetInterval target.length → BinaryFraction × ℕ)
--       (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (q : TargetInterval target.length)
--       (reader : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
--       (next : List (ℕ × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
--       (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hFb : Nat.size F + 2 ≤ B) (hF : 1 ≤ F)
--       (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) (he : exponent + 1 ≤ B)
--       (hnx : Nat.size source.length ≤ B) (hny : Nat.size target.length ≤ B)
--       (hH : Nat.size H ≤ B) (hd : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
--       (htau : tau.width ≤ B) (ha : a.width ≤ B) (hv : (initial q).1.width ≤ B)
--       (hp : (initial q).2 ≤ Rp) (hc : ∀ i r, (child i r).1.width ≤ B)
--       (hR : ∀ i r, (child i r).2 ≤ R)
--       (hr : ∀ key ∈ (queryOnlineKeysWithWork N P F hP a (initial q).1 q).1,
--         (reader key (queryOnlineRangeWithWork parent P exponent H tau child key).1).work oracle readWork ≤ W)
--       (hnext :
--         let keys := (queryOnlineKeysWithWork N P F hP a (initial q).1 q).1
--         (next keys (keys.map fun key =>
--           (reader key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle)).work oracle readWork ≤ K) :
--       (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next).work oracle readWork ≤
--         queryOnlineGatherBitBudget M P B Rp R W K
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryOnlineGatherBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.BitQuery` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork` and `OAI.EditApproximation.BinaryFraction.queryOnlineRangeWithWork` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.queryOnlineSourceGather` (the published bundle `Def_EditApproxScheme_10`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRandomSources_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QuerySourceGatherCost.lean (declaration OAI.EditApproximation.queryOnlineSourceGather_work_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open BinaryFraction

theorem queryOnlineSourceGather_work_bound {ι β α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B Rp R W K : ℕ) (hP : 0 < P)
    (tau a : BinaryFraction) (initial : TargetInterval target.length → BinaryFraction × ℕ)
    (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (q : TargetInterval target.length)
    (reader : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
    (next : List (ℕ × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hFb : Nat.size F + 2 ≤ B) (hF : 1 ≤ F)
    (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) (he : exponent + 1 ≤ B)
    (hnx : Nat.size source.length ≤ B) (hny : Nat.size target.length ≤ B)
    (hH : Nat.size H ≤ B) (hd : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (hv : (initial q).1.width ≤ B)
    (hp : (initial q).2 ≤ Rp) (hc : ∀ i r, (child i r).1.width ≤ B)
    (hR : ∀ i r, (child i r).2 ≤ R)
    (hr : ∀ key ∈ (queryOnlineKeysWithWork N P F hP a (initial q).1 q).1,
      (reader key (queryOnlineRangeWithWork parent P exponent H tau child key).1).work oracle readWork ≤ W)
    (hnext :
      let keys := (queryOnlineKeysWithWork N P F hP a (initial q).1 q).1
      (next keys (keys.map fun key =>
        (reader key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle)).work oracle readWork ≤ K) :
    (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next).work oracle readWork ≤
      queryOnlineGatherBitBudget M P B Rp R W K := by
  sorry

end EditApproximation

end OAI
end
