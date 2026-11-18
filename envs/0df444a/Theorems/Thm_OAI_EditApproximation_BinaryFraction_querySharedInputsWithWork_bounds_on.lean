-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_querySharedInputsWithWork_bounds_on
-- name    : OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:13.698864+00:00
-- url     : https://prove2.me/theorems/c4950e3a-446b-4847-82b7-e7bc826535f1
-- title:
--   OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on` of [lean/OAI/Combinatorics/EditApproximation/Queries/QuerySharedInputCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QuerySharedInputCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem querySharedInputsWithWork_bounds_on {nx ny : ℕ} (M N F Q exponent eM eF B R : ℕ)
--       (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (parent : TargetInterval nx)
--       (a value : BinaryFraction) (q : TargetInterval ny) (draw : CountedCellGroupDraws M F Q)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
--       (he : exponent + 1 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
--       (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
--       (hR : ∀ eb ∈ (queryExponentsWithWork N F a value).1,
--         ∀ cell ∈ (targetCellsWithWork
--           (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
--           (bitWordValue (naturalCeilingWithWork value).1) q).1,
--         ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ R) :
--       (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).1.length ≤
--         querySharedInputsLength M F exponent eM eF B ∧
--       (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).2 ≤
--         querySharedInputsBitBudget M F exponent eM eF B R
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.querySharedInputsBitBudget` and `OAI.EditApproximation.BinaryFraction.querySharedInputsLength` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.bitWordValue` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.inversePowerTwo`, `OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork` and `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.canonicalMulWithWork`, `OAI.EditApproximation.BinaryFraction.nat`, `OAI.EditApproximation.BinaryFraction.queryExponentsWithWork` and `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.targetCellsWithWork` (the published bundle `Def_EditApproxScheme_07`); `OAI.EditApproximation.groupDyadicScales` and `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.CountedCellGroupDraws`, `OAI.EditApproximation.groupDyadicScaleAt` and `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRefinement_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QuerySharedInputCost.lean (declaration OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem querySharedInputsWithWork_bounds_on {nx ny : ℕ} (M N F Q exponent eM eF B R : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (parent : TargetInterval nx)
    (a value : BinaryFraction) (q : TargetInterval ny) (draw : CountedCellGroupDraws M F Q)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (hR : ∀ eb ∈ (queryExponentsWithWork N F a value).1,
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork value).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ R) :
    (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).1.length ≤
      querySharedInputsLength M F exponent eM eF B ∧
    (querySharedInputsWithWork M N F Q exponent eM eF hMdef hFdef parent a value q draw).2 ≤
      querySharedInputsBitBudget M F exponent eM eF B R := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
