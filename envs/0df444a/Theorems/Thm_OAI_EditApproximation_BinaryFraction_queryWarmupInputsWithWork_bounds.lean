-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryWarmupInputsWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:28:01.719353+00:00
-- url     : https://prove2.me/theorems/4e86ea44-9beb-4a58-969a-5fc5bebbd330
-- title:
--   OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryWarmupProgramCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryWarmupProgramCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryWarmupInputsWithWork_bounds {nx ny : ℕ} (M N P F B I : ℕ)
--       (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
--       (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
--       (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
--       (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
--       (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
--       (hi : ∀ r, (initial r).1.width ≤ B) (hI : ∀ r, (initial r).2 ≤ I) :
--       (queryWarmupInputsWithWork M parent N P F a initial q).1.length ≤
--         queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2) ∧
--       (queryWarmupInputsWithWork M parent N P F a initial q).2 ≤
--         queryWarmupInputsBitBudget M P F B I
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryWarmupInputsBitBudget` and `OAI.EditApproximation.BinaryFraction.queryWarmupRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork` (the published bundle `Def_EditApproxScheme_07`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryWarmupProgram_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryWarmupProgramCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
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

theorem queryWarmupInputsWithWork_bounds {nx ny : ℕ} (M N P F B I : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hI : ∀ r, (initial r).2 ≤ I) :
    (queryWarmupInputsWithWork M parent N P F a initial q).1.length ≤
      queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2) ∧
    (queryWarmupInputsWithWork M parent N P F a initial q).2 ≤
      queryWarmupInputsBitBudget M P F B I := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
