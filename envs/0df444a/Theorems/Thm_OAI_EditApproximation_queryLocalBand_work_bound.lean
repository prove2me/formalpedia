-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryLocalBand_work_bound
-- name    : OAI.EditApproximation.queryLocalBand_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:46.507972+00:00
-- url     : https://prove2.me/theorems/6f4a7df7-0cb7-4bee-b1e5-bfa6c9191334
-- title:
--   OAI.EditApproximation.queryLocalBand_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryLocalBand_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalBandCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalBandCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryLocalBand_work_bound (Rp W : ℕ)
--       (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
--         N P F exponent H Q eM eF B E S (t - 1) tau a eta kappa delta (fun _ _ => 0))
--       (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
--       (hp : ∀ r, (parentInitial r).2 ≤ Rp)
--       (hpW : ∀ r, (parentInitial r).1.width ≤ B)
--       (hpN : ∀ r, 0 ≤ (parentInitial r).1.value)
--       (hmW : ∀ key, ((readMass key).value oracle).width ≤ B)
--       (hiW : ∀ key, ((readInitial key).value oracle).width ≤ B)
--       (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
--       (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
--       (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
--       (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
--       (hiN : ∀ key, 0 ≤ ((readInitial key).value oracle).value)
--       (heN : ∀ key, 0 ≤ ((readEarlier key).value oracle).value)
--       (heI : ∀ key, ((readEarlier key).value oracle).value ≤
--         ((readInitial (key.1, key.2.2)).value oracle).value)
--       (hmR : ∀ key, (readMass key).work oracle readWork ≤ W)
--       (hiR : ∀ key, (readInitial key).work oracle readWork ≤ W)
--       (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
--         (readGroup key).work oracle readWork ≤ W)
--       (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
--         (readInteger key range).work oracle readWork ≤ W)
--       (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
--       (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W) :
--       (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
--         tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger
--         q readEarlier readCurrent).work oracle readWork ≤
--         queryLocalBandBitBudget M N P F exponent eM eF B S t Rp W
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryLocalBand`, `OAI.EditApproximation.BinaryFraction.PreparedKernelNumericBounds` and `OAI.EditApproximation.BinaryFraction.queryLocalBandBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.queryGroupKeySize` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.BitQuery` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.GroupScalarKey` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryFamilyBoundedActive_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalBandCost.lean (declaration OAI.EditApproximation.queryLocalBand_work_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalBand_work_bound (Rp W : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E S (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpW : ∀ r, (parentInitial r).1.width ≤ B)
    (hpN : ∀ r, 0 ≤ (parentInitial r).1.value)
    (hmW : ∀ key, ((readMass key).value oracle).width ≤ B)
    (hiW : ∀ key, ((readInitial key).value oracle).width ≤ B)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hiN : ∀ key, 0 ≤ ((readInitial key).value oracle).value)
    (heN : ∀ key, 0 ≤ ((readEarlier key).value oracle).value)
    (heI : ∀ key, ((readEarlier key).value oracle).value ≤
      ((readInitial (key.1, key.2.2)).value oracle).value)
    (hmR : ∀ key, (readMass key).work oracle readWork ≤ W)
    (hiR : ∀ key, (readInitial key).work oracle readWork ≤ W)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W) :
    (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger
      q readEarlier readCurrent).work oracle readWork ≤
      queryLocalBandBitBudget M N P F exponent eM eF B S t Rp W := by
  sorry

end Band
end EditApproximation

end OAI
end
