-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryEarlierRepresentativesWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:28:11.502114+00:00
-- url     : https://prove2.me/theorems/e60f3ec9-57ab-4cab-a922-340d23f0c495
-- title:
--   OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryRepresentativeCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRepresentativeCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryEarlierRepresentativesWithWork_bounds {n : ℕ} (N P F exponent B R : ℕ)
--       (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
--       (q : TargetInterval n) (hB : 8 ≤ B) (hN : Nat.size N ≤ B)
--       (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B)
--       (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
--       (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
--       (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
--       (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1.length ≤
--         queryEarlierRepresentativesLength P F exponent B ∧
--       (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).2 ≤
--         queryEarlierRepresentativesBitBudget P F exponent B R
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesBitBudget` and `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesLength` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork` (the published bundle `Def_EditApproxScheme_09`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork_bounds` and `OAI.EditApproximation.queryLocalBand_work_bound` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRepresentativeCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryEarlierRepresentativesWithWork_bounds {n : ℕ} (N P F exponent B R : ℕ)
    (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (q : TargetInterval n) (hB : 8 ≤ B) (hN : Nat.size N ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B)
    (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1.length ≤
      queryEarlierRepresentativesLength P F exponent B ∧
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).2 ≤
      queryEarlierRepresentativesBitBudget P F exponent B R := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
