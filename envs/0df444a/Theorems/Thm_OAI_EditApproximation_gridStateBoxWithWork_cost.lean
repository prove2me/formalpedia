-- Prove2me | Theorems.Thm_OAI_EditApproximation_gridStateBoxWithWork_cost
-- name    : OAI.EditApproximation.gridStateBoxWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:05.106706+00:00
-- url     : https://prove2.me/theorems/0debea04-8e86-49ef-9ca0-9bda838f3a4a
-- title:
--   OAI.EditApproximation.gridStateBoxWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.gridStateBoxWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalGridWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalGridWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem gridStateBoxWithWork_cost (n g radius lo hi B : ℕ) (hg : 0 < g)
--       (hn : Nat.size n ≤ B) (hgs : Nat.size g ≤ B) (hr : Nat.size radius ≤ B)
--       (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
--       (gridStateBoxWithWork n g radius lo hi).2 ≤
--         gridStateBoxBitBudget (2 * radius / g + 2) B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.gridStateBoxBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.gridStateBoxWithWork` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_cost` and `OAI.EditApproximation.BinaryFraction.wideActionGridWithWork_complete_cost` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryLocalGridWork.lean (declaration OAI.EditApproximation.gridStateBoxWithWork_cost)

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

theorem gridStateBoxWithWork_cost (n g radius lo hi B : ℕ) (hg : 0 < g)
    (hn : Nat.size n ≤ B) (hgs : Nat.size g ≤ B) (hr : Nat.size radius ≤ B)
    (hl : Nat.size lo ≤ B) (hh : Nat.size hi ≤ B) :
    (gridStateBoxWithWork n g radius lo hi).2 ≤
      gridStateBoxBitBudget (2 * radius / g + 2) B := by
  sorry

end EditApproximation

end OAI
end
