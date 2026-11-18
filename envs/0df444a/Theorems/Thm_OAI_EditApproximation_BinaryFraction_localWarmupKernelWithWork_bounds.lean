-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_localWarmupKernelWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:45.892038+00:00
-- url     : https://prove2.me/theorems/57314005-b2cc-4c8e-8d6c-2ddd72f523d3
-- title:
--   OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalWarmupWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalWarmupWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem localWarmupKernelWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
--       (N P F B : ℕ) (hP : 0 < P) (hFpos : 1 ≤ F) (a : BinaryFraction)
--       (initial : TargetInterval ny → BinaryFraction) (child : Fin M × TargetInterval ny → BinaryFraction)
--       (query : TargetInterval ny) (hB : 10 ≤ B) (hN : Nat.size N ≤ B)
--       (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
--       (hM : Nat.size M ≤ B) (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
--       (localWarmupKernelWithWork parent N P F a initial child query).1.width ≤ localWarmupWordBudget M B ∧
--         (localWarmupKernelWithWork parent N P F a initial child query).2 ≤ localWarmupBitBudget M P F B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.localWarmupBitBudget`, `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork` and `OAI.EditApproximation.BinaryFraction.localWarmupWordBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.queryChargedFamilyTable_width` and `OAI.EditApproximation.queryWarmupProgram_work_bound` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalWarmupWork.lean (declaration OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds)

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

attribute [local irreducible] localRepresentativesWithWork wideActionsFromRepresentativesWithWork

theorem localWarmupKernelWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F B : ℕ) (hP : 0 < P) (hFpos : 1 ≤ F) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction) (child : Fin M × TargetInterval ny → BinaryFraction)
    (query : TargetInterval ny) (hB : 10 ≤ B) (hN : Nat.size N ≤ B)
    (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
    (localWarmupKernelWithWork parent N P F a initial child query).1.width ≤ localWarmupWordBudget M B ∧
      (localWarmupKernelWithWork parent N P F a initial child query).2 ≤ localWarmupBitBudget M P F B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
