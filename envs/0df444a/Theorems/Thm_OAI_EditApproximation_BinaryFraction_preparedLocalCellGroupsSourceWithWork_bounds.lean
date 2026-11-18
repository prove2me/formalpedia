-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedLocalCellGroupsSourceWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:35.495399+00:00
-- url     : https://prove2.me/theorems/f3e94dc5-1f82-436b-9a3c-5c65e6b994b1
-- title:
--   OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinarySourceSelectorBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinarySourceSelectorBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem preparedLocalCellGroupsSourceWithWork_bounds (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
--       (hn : ∀ input, (current input).2 ≤ R) (D : ℕ)
--       (hd : ∀ eb ∈ List.range (max 1 N.bits.length),
--         (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
--         ∀ cell ∈ (targetCellsWithWork
--           (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
--           (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
--         ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ D) :
--       let selected := preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF
--         hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N draw q
--       selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
--       selected.2 ≤ preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor R * (D + 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.PreparedKernelInputBounds`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork`, `OAI.EditApproximation.BinaryFraction.preparedLocalGroupsBitBudget` and `OAI.EditApproximation.BinaryFraction.tableReadFactor` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction`, `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.bitWordValue` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.inversePowerTwo` and `OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.canonicalMulWithWork`, `OAI.EditApproximation.BinaryFraction.nat` and `OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.targetCellsWithWork` (the published bundle `Def_EditApproxScheme_07`); `OAI.EditApproximation.groupDyadicScales` and `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.CellGroupReadDraws` and `OAI.EditApproximation.groupDyadicScaleAt` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRefinement_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinarySourceSelectorBounds.lean (declaration OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (old current : Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (t : ℕ) (draw : CellGroupReadDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S t
    tau a eta kappa delta (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun s => (old s).1) (fun s => (current s).1) (fun s i => (history s i).1)
    (fun b r => (integer b r).1))
  (hp : ∀ r, (parentInitial r).2 ≤ R)

include hb hp in
theorem preparedLocalCellGroupsSourceWithWork_bounds (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hn : ∀ input, (current input).2 ≤ R) (D : ℕ)
    (hd : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ D) :
    let selected := preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N draw q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    selected.2 ≤ preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor R * (D + 4) := by
  sorry

end Selectors
end EditApproximation.BinaryFraction

end OAI
end
