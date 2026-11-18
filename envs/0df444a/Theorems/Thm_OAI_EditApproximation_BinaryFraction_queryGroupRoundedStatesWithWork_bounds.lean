-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupRoundedStatesWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:27:16.736538+00:00
-- url     : https://prove2.me/theorems/cea9120a-4ce0-456f-a3db-a04b41528d9d
-- title:
--   OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryRoundedStateCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRoundedStateCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryGroupRoundedStatesWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
--       (b exponent B left right : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : BinaryFraction)
--       (hB : 4 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
--       (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hc : Nat.size cell.1 ≤ B)
--       (he : exponent + 1 ≤ B) (hh : h.width ≤ B)
--       (hleft : 2 * (12 * b) / groupRoundSpacing exponent h.value + 2 ≤ left)
--       (hright : 2 * ⌈2 * h.value⌉₊ / groupRoundSpacing exponent h.value + 2 ≤ right) :
--       (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1.length ≤ left * right ∧
--       (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 ≤
--         queryRoundedStatesBitBudget left right exponent B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryRoundedStatesBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.groupRoundSpacing` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork` (the published bundle `Def_EditApproxScheme_07`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRoundedStateCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds)

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

theorem queryGroupRoundedStatesWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent B left right : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : BinaryFraction)
    (hB : 4 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hc : Nat.size cell.1 ≤ B)
    (he : exponent + 1 ≤ B) (hh : h.width ≤ B)
    (hleft : 2 * (12 * b) / groupRoundSpacing exponent h.value + 2 ≤ left)
    (hright : 2 * ⌈2 * h.value⌉₊ / groupRoundSpacing exponent h.value + 2 ≤ right) :
    (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1.length ≤ left * right ∧
    (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 ≤
      queryRoundedStatesBitBudget left right exponent B := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
