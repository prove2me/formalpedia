-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_wideActionGridWithWork_complete_cost
-- name    : OAI.EditApproximation.BinaryFraction.wideActionGridWithWork_complete_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:54.500407+00:00
-- url     : https://prove2.me/theorems/1188d7f3-9766-4082-b08b-9ea355fcadcd
-- title:
--   OAI.EditApproximation.BinaryFraction.wideActionGridWithWork_complete_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.wideActionGridWithWork_complete_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedRepresentativeWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedRepresentativeWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem wideActionGridWithWork_complete_cost {nx ny : ℕ} (M : ℕ)
--       (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
--       (hPpos : 0 < P) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
--       (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
--       (wideActionGridWithWork M parent center b P).2 ≤ wideMaterializationBitBudget M P B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.wideMaterializationBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.wideActionGridWithWork` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedRepresentativeWork.lean (declaration OAI.EditApproximation.BinaryFraction.wideActionGridWithWork_complete_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem wideActionGridWithWork_complete_cost {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
    (hPpos : 0 < P) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B) :
    (wideActionGridWithWork M parent center b P).2 ≤ wideMaterializationBitBudget M P B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
