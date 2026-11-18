-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_unskippedGuardWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:28:47.208662+00:00
-- url     : https://prove2.me/theorems/f0b564c4-260c-4187-a99e-19d70104f01e
-- title:
--   OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryUnskippedGuardWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryUnskippedGuardWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem unskippedGuardWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
--       (center : TargetInterval ny) (b e : ℕ) (F : BinaryFraction)
--       (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
--       (initial : Fin M → TargetInterval ny → BinaryFraction) (B : ℕ)
--       (hF : F.width ≤ B) (hb : Nat.size b + 2 ≤ B)
--       (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
--       (hi : ∀ action ∈ band, ∀ i, (initial i (action i)).width ≤ B) :
--       (unskippedGuardWithWork parent center b e F band wide hne initial).2 ≤
--         unskippedGuardBitBudget e b M band.length wide.length B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.unskippedGuardBitBudget` and `OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryUnskippedGuardWork.lean (declaration OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_cost)

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

theorem unskippedGuardWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (b e : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) (B : ℕ)
    (hF : F.width ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hi : ∀ action ∈ band, ∀ i, (initial i (action i)).width ≤ B) :
    (unskippedGuardWithWork parent center b e F band wide hne initial).2 ≤
      unskippedGuardBitBudget e b M band.length wide.length B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
