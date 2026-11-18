-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_physicalContinuationWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:28:22.444494+00:00
-- url     : https://prove2.me/theorems/a883fe27-b246-4d6e-a827-405e6ae84999
-- title:
--   OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPhysicalContinuationWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPhysicalContinuationWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem physicalContinuationWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
--       (representatives : List (ℕ × TargetInterval ny)) (P F B : ℕ)
--       (delta fallback : BinaryFraction) (old current : Fin M × TargetInterval ny → BinaryFraction)
--       (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
--       (query : TargetInterval ny) (hPpos : 0 < P) (hB : 10 ≤ B)
--       (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
--       (hM : Nat.size M ≤ B) (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (hrep : ∀ br ∈ representatives, Nat.size br.1 ≤ B)
--       (hdelta : delta.width ≤ B) (hfallback : fallback.width ≤ B)
--       (hold : ∀ s, (old s).width ≤ B) (hcurrent : ∀ s, (current s).width ≤ B)
--       (hgroups : ∀ action ∈ groups, action.connection.width ≤ connectionWordBudget M B)
--       (honline : ∀ action ∈ online, action.connection.width ≤ connectionWordBudget M B) :
--       (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).1.width ≤
--           localContinuationWordBudget M (physicalContinuationInputBudget M B) ∧
--         (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).2 ≤
--           physicalContinuationBitBudget M P representatives.length groups.length online.length B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.connectionWordBudget`, `OAI.EditApproximation.BinaryFraction.localContinuationWordBudget`, `OAI.EditApproximation.BinaryFraction.physicalContinuationBitBudget`, `OAI.EditApproximation.BinaryFraction.physicalContinuationInputBudget` and `OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction` and `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPhysicalContinuationWork.lean (declaration OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds)

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

theorem physicalContinuationWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F B : ℕ)
    (delta fallback : BinaryFraction) (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (hPpos : 0 < P) (hB : 10 ≤ B)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hrep : ∀ br ∈ representatives, Nat.size br.1 ≤ B)
    (hdelta : delta.width ≤ B) (hfallback : fallback.width ≤ B)
    (hold : ∀ s, (old s).width ≤ B) (hcurrent : ∀ s, (current s).width ≤ B)
    (hgroups : ∀ action ∈ groups, action.connection.width ≤ connectionWordBudget M B)
    (honline : ∀ action ∈ online, action.connection.width ≤ connectionWordBudget M B) :
    (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).1.width ≤
        localContinuationWordBudget M (physicalContinuationInputBudget M B) ∧
      (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).2 ≤
        physicalContinuationBitBudget M P representatives.length groups.length online.length B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
