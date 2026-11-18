-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_bellmanWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.bellmanWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:09.253909+00:00
-- url     : https://prove2.me/theorems/8339a686-feff-4cd1-8cbd-72b1e339cb0f
-- title:
--   OAI.EditApproximation.BinaryFraction.bellmanWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.bellmanWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBellmanKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBellmanKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`, with `open Finset`):
--
--   ```lean
--   theorem bellmanWithWork_bounds {Parent Child : Type*} {M : ℕ}
--       (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
--       (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M))
--       (B F C : ℕ) (hL : L.width ≤ B) (hf : fallback.width ≤ F)
--       (hd : ∀ action ∈ actions, (distance query action.center).1.width ≤ B)
--       (hdc : ∀ action ∈ actions, (distance query action.center).2 ≤ C)
--       (hc : ∀ action ∈ actions, action.connection.width ≤ B)
--       (hv : ∀ action ∈ actions, ∀ i, (child (action.childState i)).width ≤ B) :
--       (bellmanWithWork distance L fallback child query actions).1.width ≤ F + bellmanActionWordBudget M B ∧
--         (bellmanWithWork distance L fallback child query actions).2 ≤ bellmanBitBudget M actions.length B F C
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.bellmanActionWordBudget`, `OAI.EditApproximation.BinaryFraction.bellmanBitBudget` and `OAI.EditApproximation.BinaryFraction.bellmanWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction` and `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBellmanKernel.lean (declaration OAI.EditApproximation.BinaryFraction.bellmanWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace BinaryFraction

open Finset

theorem bellmanWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M))
    (B F C : ℕ) (hL : L.width ≤ B) (hf : fallback.width ≤ F)
    (hd : ∀ action ∈ actions, (distance query action.center).1.width ≤ B)
    (hdc : ∀ action ∈ actions, (distance query action.center).2 ≤ C)
    (hc : ∀ action ∈ actions, action.connection.width ≤ B)
    (hv : ∀ action ∈ actions, ∀ i, (child (action.childState i)).width ≤ B) :
    (bellmanWithWork distance L fallback child query actions).1.width ≤ F + bellmanActionWordBudget M B ∧
      (bellmanWithWork distance L fallback child query actions).2 ≤ bellmanBitBudget M actions.length B F C := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
