-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_gradientCellWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:04.731192+00:00
-- url     : https://prove2.me/theorems/f0501020-a42d-4199-9f01-6ca98b5bfceb
-- title:
--   OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryGradientWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryGradientWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem gradientCellWithWork_cost {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
--       (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
--       (gradientCellWithWork G linear point i).2 ≤
--         gradientCellBitBudget G (point.get i).width (linear.get i).width
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.gradientCellBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.gradientCellWithWork` and `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryGradientWork.lean (declaration OAI.EditApproximation.BinaryFraction.gradientCellWithWork_cost)

import Mathlib
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem gradientCellWithWork_cost {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCellWithWork G linear point i).2 ≤
      gradientCellBitBudget G (point.get i).width (linear.get i).width := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
