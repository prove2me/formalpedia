-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_localRepresentativesWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:23.732874+00:00
-- url     : https://prove2.me/theorems/d62c080c-b38d-472e-93c9-5aa06ba2e155
-- title:
--   OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalRepresentativeWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalRepresentativeWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem localRepresentativesWithWork_cost {n : ℕ} (N P F B : ℕ) (a : BinaryFraction)
--       (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n)
--       (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (hFpos : 1 ≤ F) (hPbits : Nat.size P ≤ B) (hP : 0 < P) (hn : Nat.size n ≤ B)
--       (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) :
--       (localRepresentativesWithWork N P F a initial query).2 ≤ localRepresentativesBitBudget P F B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.localRepresentativesBitBudget` and `OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalRepresentativeWork.lean (declaration OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem localRepresentativesWithWork_cost {n : ℕ} (N P F B : ℕ) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPbits : Nat.size P ≤ B) (hP : 0 < P) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) :
    (localRepresentativesWithWork N P F a initial query).2 ≤ localRepresentativesBitBudget P F B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
