-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupSourceKeysWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:27:19.469212+00:00
-- url     : https://prove2.me/theorems/71db2a78-2767-4c91-82f1-549f8a8bac15
-- title:
--   OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryGroupSourceCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryGroupSourceCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryGroupSourceKeysWithWork_bounds {n : ℕ} (M N F Q exponent eM eF B : ℕ)
--       (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
--       (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
--       (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
--       (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1.length ≤
--         queryGroupSourceKeysLength M F exponent eM eF B ∧
--       (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).2 ≤
--         queryGroupSourceKeysBitBudget M F exponent eM eF B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysBitBudget` and `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysLength` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.GroupScalarKey` and `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRandomSources_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryGroupSourceCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds)

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

namespace EditApproximation.BinaryFraction

theorem queryGroupSourceKeysWithWork_bounds {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1.length ≤
      queryGroupSourceKeysLength M F exponent eM eF B ∧
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).2 ≤
      queryGroupSourceKeysBitBudget M F exponent eM eF B := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
