-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_unskippedEstimateWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:08.290895+00:00
-- url     : https://prove2.me/theorems/78f807a1-4b50-4f7f-b739-fcdd140ecc23
-- title:
--   OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinarySampledGroupWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinarySampledGroupWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem unskippedEstimateWithWork_bounds {α : Type*} (source target : List α) {M T : ℕ}
--       (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
--       (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
--       (scales : Fin T → BinaryFraction)
--       (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
--       (member : UnskippedBand source target parent b P exponent tau.value F.value
--         (fun i q => (child i q).value) (fun i q => (initial i q).value))
--       (B : ℕ) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
--       (hb : Nat.size b + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
--       (hs : ∀ t, (scales t).width ≤ B)
--       (hi : ∀ action ∈ member.actions, ∀ i, (initial i (action i)).width ≤ B)
--       (hv : ∀ i q, (current i q).width ≤ B) :
--       (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current
--         scales draw member).1.width ≤ sampledMemberWordBudget M T b B ∧
--       (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current
--         scales draw member).2 ≤ sampledMemberBitBudget M T exponent b member.actions.length B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.sampledMemberBitBudget`, `OAI.EditApproximation.BinaryFraction.sampledMemberWordBudget` and `OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.UnskippedBand.actions` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinarySampledGroupWork.lean (declaration OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem unskippedEstimateWithWork_bounds {α : Type*} (source target : List α) {M T : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (scales : Fin T → BinaryFraction)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
    (member : UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).value))
    (B : ℕ) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hs : ∀ t, (scales t).width ≤ B)
    (hi : ∀ action ∈ member.actions, ∀ i, (initial i (action i)).width ≤ B)
    (hv : ∀ i q, (current i q).width ≤ B) :
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1.width ≤ sampledMemberWordBudget M T b B ∧
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤ sampledMemberBitBudget M T exponent b member.actions.length B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
