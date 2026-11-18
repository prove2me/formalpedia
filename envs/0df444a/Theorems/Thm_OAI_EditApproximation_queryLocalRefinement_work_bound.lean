-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryLocalRefinement_work_bound
-- name    : OAI.EditApproximation.queryLocalRefinement_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:31:22.491237+00:00
-- url     : https://prove2.me/theorems/c8898406-f673-40d3-ae2b-35387fef63df
-- title:
--   OAI.EditApproximation.queryLocalRefinement_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryLocalRefinement_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalRefinementCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalRefinementCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryLocalRefinement_work_bound (Rp W Dg Do : ℕ)
--       (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
--       (hp : ∀ r, (parentInitial r).2 ≤ Rp)
--       (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
--       (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
--       (heR : ∀ key ∈ (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1,
--         (readEarlier key).work oracle readWork ≤ W)
--       (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
--       (hdg : ∀ eb ∈ List.range (max 1 N.bits.length),
--         (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
--         ∀ cell ∈ (targetCellsWithWork
--           (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
--           (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
--         ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ Dg)
--       (hdo : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
--         (centerEligibilityWithWork (2 ^ e) F a
--           (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
--             (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
--           (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
--             (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ Do)
--       (hb :
--         let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
--         let earlierWords := earlier.map fun key => (readEarlier key).value oracle
--         let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
--           (parentInitial q).1 q draw).1
--         let sharedWords := shared.map fun key => (readCurrent key).value oracle
--         PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
--           tau a eta kappa delta (fun r => (parentInitial r).1)
--           (fun i r => (child i r).1) (fun i r => (initial i r).1)
--           (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
--           (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
--           (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
--           (fun b r => (integer b r).1)) :
--       (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
--         parentInitial child initial R hc hi draw integer q readEarlier readCurrent).work oracle readWork ≤
--         queryLocalRefinementBitBudget M N P F exponent eM eF B S t Rp R W Dg Do
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryLocalRefinement`, `OAI.EditApproximation.seedGridSpacingWithWork_pos`, `OAI.EditApproximation.BinaryFraction.PreparedKernelInputBounds` and `OAI.EditApproximation.BinaryFraction.queryLocalRefinementBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BitQuery` and `OAI.EditApproximation.bitWordValue` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.seedGridSpacingWithWork` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.inversePowerTwo`, `OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork` and `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.canonicalMulWithWork`, `OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork`, `OAI.EditApproximation.BinaryFraction.nat`, `OAI.EditApproximation.BinaryFraction.queryExponentsWithWork` and `OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryChildReadWithWork`, `OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork` and `OAI.EditApproximation.BinaryFraction.targetCellsWithWork` (the published bundle `Def_EditApproxScheme_07`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount` and `OAI.EditApproximation.roundStateWithWork` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.CountedCellGroupDraws`, `OAI.EditApproximation.groupDyadicScaleAt` and `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryLocalRandomSources_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalRefinementCost.lean (declaration OAI.EditApproximation.queryLocalRefinement_work_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalRefinement_work_bound (Rp W Dg Do : ℕ)
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (heR : ∀ key ∈ (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1,
      (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
    (hdg : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ Dg)
    (hdo : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ Do)
    (hb :
      let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
      let earlierWords := earlier.map fun key => (readEarlier key).value oracle
      let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
        (parentInitial q).1 q draw).1
      let sharedWords := shared.map fun key => (readCurrent key).value oracle
      PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
        tau a eta kappa delta (fun r => (parentInitial r).1)
        (fun i r => (child i r).1) (fun i r => (initial i r).1)
        (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
        (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
        (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
        (fun b r => (integer b r).1)) :
    (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      parentInitial child initial R hc hi draw integer q readEarlier readCurrent).work oracle readWork ≤
      queryLocalRefinementBitBudget M N P F exponent eM eF B S t Rp R W Dg Do := by
  sorry

end Local
end EditApproximation

end OAI
end
