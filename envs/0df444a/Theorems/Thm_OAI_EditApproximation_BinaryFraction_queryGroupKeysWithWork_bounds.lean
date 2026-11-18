-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupKeysWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:07.817469+00:00
-- url     : https://prove2.me/theorems/e4924d7e-4d0e-4ac6-bd66-cf0babaa274c
-- title:
--   OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryGroupKeyCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryGroupKeyCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryGroupKeysWithWork_bounds {n : ℕ} (N F exponent B : ℕ)
--       (a value : BinaryFraction) (q : TargetInterval n)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (hFpos : 1 ≤ F) (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B)
--       (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
--       (queryGroupKeysWithWork N F exponent a value q).1.length ≤
--         (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
--       (queryGroupKeysWithWork N F exponent a value q).2 ≤ queryGroupKeysBitBudget F exponent B ∧
--       ∀ key ∈ (queryGroupKeysWithWork N F exponent a value q).1,
--         Nat.size key.1 ≤ B + 1 ∧ (∃ e : ℕ, key.1 = 2 ^ e) ∧
--         Nat.size key.2.1 ≤ 16 * B + 183 ∧ Nat.size key.2.2 ≤ 16 * B + 183
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryGroupKeysBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork` (the published bundle `Def_EditApproxScheme_07`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds` and `OAI.EditApproximation.queryLocalRandomSources_work_bound` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryGroupKeyCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryGroupKeysWithWork_bounds {n : ℕ} (N F exponent B : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    (queryGroupKeysWithWork N F exponent a value q).1.length ≤
      (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    (queryGroupKeysWithWork N F exponent a value q).2 ≤ queryGroupKeysBitBudget F exponent B ∧
    ∀ key ∈ (queryGroupKeysWithWork N F exponent a value q).1,
      Nat.size key.1 ≤ B + 1 ∧ (∃ e : ℕ, key.1 = 2 ^ e) ∧
      Nat.size key.2.1 ≤ 16 * B + 183 ∧ Nat.size key.2.2 ≤ 16 * B + 183 := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
