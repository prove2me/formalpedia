-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupSelectWithWork_value
-- name    : OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:55.265649+00:00
-- url     : https://prove2.me/theorems/22b9023f-860d-4d7e-8017-85a18e904ab1
-- title:
--   OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSelectors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSelectors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryGroupSelectWithWork_value (draw : CountedCellGroupDraws M F Q)
--       (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
--       (q : TargetInterval target.length) :
--       ((queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
--         parentInitial child initial R hc hi draw keys words q).1.map BinaryBellmanAction.decode) =
--         localCellGroupActions source target parent N P F exponent Q tau.value a.value
--           (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
--           (fun i r => (initial i r).1.value)
--           (fun i r => finiteAnswerTable keys (words.map value) (i, r))
--           (fun b cell scale sample => (draw b cell scale sample).1) q
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryBellmanAction.decode` and `OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction`, `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.RationalBellmanAction` and `OAI.EditApproximation.finiteAnswerTable` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount` and `OAI.EditApproximation.instDecidableEqTargetInterval` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.CountedCellGroupDraws` and `OAI.EditApproximation.groupDyadicScaleAt` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.localCellGroupActions` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRandomSources_refines` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSelectors.lean (declaration OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork_value)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

theorem queryGroupSelectWithWork_value (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    ((queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi draw keys words q).1.map BinaryBellmanAction.decode) =
      localCellGroupActions source target parent N P F exponent Q tau.value a.value
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (fun i r => finiteAnswerTable keys (words.map value) (i, r))
        (fun b cell scale sample => (draw b cell scale sample).1) q := by
  sorry

end Selectors
end BinaryFraction
end EditApproximation

end OAI
end
