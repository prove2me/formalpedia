-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryLocalRandomSources_work_bound
-- name    : OAI.EditApproximation.queryLocalRandomSources_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:09.418222+00:00
-- url     : https://prove2.me/theorems/dc468961-7b2e-43c2-af61-5466607a4f16
-- title:
--   OAI.EditApproximation.queryLocalRandomSources_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryLocalRandomSources_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSourcesCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSourcesCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryLocalRandomSources_work_bound (Rp W : ℕ)
--       (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
--       (hp : ∀ r, (parentInitial r).2 ≤ Rp)
--       (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
--       (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
--       (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
--       (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
--       (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
--         (readGroup key).work oracle readWork ≤ W)
--       (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
--         (readInteger key range).work oracle readWork ≤ W)
--       (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
--       (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
--       (hb :
--         let groupKeys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
--         let groupWords := groupKeys.map fun key => (readGroup key).value oracle
--         let onlineKeys := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
--         let onlineWords := onlineKeys.map fun key =>
--           (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
--         let draw := queryGroupDrawReadWithWork groupKeys groupWords
--         let integer := queryOnlineIntegerReadWithWork onlineKeys onlineWords
--         let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
--         let earlierWords := earlier.map fun key => (readEarlier key).value oracle
--         let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
--           (parentInitial q).1 q draw).1
--         let sharedWords := shared.map fun key => (readCurrent key).value oracle
--         PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
--           tau a eta kappa delta (fun r => (parentInitial r).1)
--           (fun i r => (child i r).1) (fun i r => (initial i r).1)
--           (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
--           (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
--           (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
--           (fun b r => (integer b r).1)) :
--       (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
--         tau a eta kappa delta t parentInitial child initial R hc hi q
--         readGroup readInteger readEarlier readCurrent).work oracle readWork ≤
--         queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp R W
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryLocalRandomSources`, `OAI.EditApproximation.BinaryFraction.PreparedKernelInputBounds` and `OAI.EditApproximation.BinaryFraction.queryLocalSourcesBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.queryGroupKeySize` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.BitQuery` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryChildReadWithWork`, `OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork` and `OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadWithWork` (the published bundle `Def_EditApproxScheme_07`); `OAI.EditApproximation.groupDyadicScales` and `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork`, `OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork` and `OAI.EditApproximation.BinaryFraction.queryOnlineRangeWithWork` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.GroupScalarKey`, `OAI.EditApproximation.groupDyadicScaleAt`, `OAI.EditApproximation.BinaryFraction.queryGroupDrawReadWithWork`, `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork` and `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalBand_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSourcesCost.lean (declaration OAI.EditApproximation.queryLocalRandomSources_work_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalRandomSources_work_bound (Rp W : ℕ)
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
    (hb :
      let groupKeys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
      let groupWords := groupKeys.map fun key => (readGroup key).value oracle
      let onlineKeys := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
      let onlineWords := onlineKeys.map fun key =>
        (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
      let draw := queryGroupDrawReadWithWork groupKeys groupWords
      let integer := queryOnlineIntegerReadWithWork onlineKeys onlineWords
      let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
      let earlierWords := earlier.map fun key => (readEarlier key).value oracle
      let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
        (parentInitial q).1 q draw).1
      let sharedWords := shared.map fun key => (readCurrent key).value oracle
      PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
        tau a eta kappa delta (fun r => (parentInitial r).1)
        (fun i r => (child i r).1) (fun i r => (initial i r).1)
        (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
        (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
        (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
        (fun b r => (integer b r).1)) :
    (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi q
      readGroup readInteger readEarlier readCurrent).work oracle readWork ≤
      queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp R W := by
  sorry

end Sources
end EditApproximation

end OAI
end
