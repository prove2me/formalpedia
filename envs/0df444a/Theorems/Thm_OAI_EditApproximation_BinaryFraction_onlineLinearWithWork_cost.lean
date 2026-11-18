-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_onlineLinearWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.onlineLinearWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:24.324226+00:00
-- url     : https://prove2.me/theorems/d8bf83f5-b684-4808-9f51-3d58a328d629
-- title:
--   OAI.EditApproximation.BinaryFraction.onlineLinearWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.onlineLinearWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryOnlineInputWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryOnlineInputWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem onlineLinearWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
--       (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
--       (t : ℕ) (i : β × σ) (Be Bk Bm Bt : ℕ)
--       (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk) (hm : (mass i.1).width ≤ Bm)
--       (ht : ∀ s ≤ t + 1, (table s i).width ≤ Bt) :
--       (onlineLinearWithWork mass table eta kappa t i).2 ≤ onlineLinearBitBudget Be Bk Bm Bt t
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.onlineLinearBitBudget` and `OAI.EditApproximation.BinaryFraction.onlineLinearWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryOnlineInputWork.lean (declaration OAI.EditApproximation.BinaryFraction.onlineLinearWithWork_cost)

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

theorem onlineLinearWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (Be Bk Bm Bt : ℕ)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk) (hm : (mass i.1).width ≤ Bm)
    (ht : ∀ s ≤ t + 1, (table s i).width ≤ Bt) :
    (onlineLinearWithWork mass table eta kappa t i).2 ≤ onlineLinearBitBudget Be Bk Bm Bt t := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
