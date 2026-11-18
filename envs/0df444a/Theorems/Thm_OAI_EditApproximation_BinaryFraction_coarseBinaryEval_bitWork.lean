-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_coarseBinaryEval_bitWork
-- name    : OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:37.42414+00:00
-- url     : https://prove2.me/theorems/7bf2790e-c463-41eb-b09f-96541eb8f7bd
-- title:
--   OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork` of [lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseBinaryBitWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseBinaryBitWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem coarseBinaryEval_bitWork {B d : ℕ} {α : Type*} [DecidableEq α]
--       (k q L N R D A : ℕ) (frame : List (Option α)) (two : BinaryFraction)
--       (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
--       (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (htwo : two.value = 2)
--       (htw : two.width ≤ A) (hd : Nat.size two.representation.den ≤ D)
--       (hroot : two.representation.den = coarseCommonDenominator 1 q L B R)
--       (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
--       (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
--       (hbound : Nat.size (coarseLevelMagnitude N k B R + 2) + 2 * D + 1 ≤ A)
--       (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction) (start : ℕ)
--       (ha : CoarseGridCell two allowance k D A)
--       (hpath : allowance.value.den ∣ (L * B * q) ^ j)
--       (hstart : start + tree.word.length ≤ N) :
--       CoarseBinaryBox two (2 * k + 1) (coarseLevelMagnitude N k B d) D A
--         (coarseBinaryEval k q L frame two tree draws allowance start).1 ∧
--       (coarseBinaryEval k q L frame two tree draws allowance start).2 ≤
--         (100000000 * (A + 1) ^ 2) * coarseBinaryWeight k q L tree draws allowance
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.CoarseBinaryBox`, `OAI.EditApproximation.BinaryFraction.CoarseGridCell`, `OAI.EditApproximation.BinaryFraction.coarseBinaryEval`, `OAI.EditApproximation.BinaryFraction.coarseBinaryWeight` and `OAI.EditApproximation.BinaryFraction.coarseLevelMagnitude` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.UnreducedRational` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws` and `OAI.EditApproximation.coarseCommonDenominator` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.CoarseBinaryArray` and `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.representation` and `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.CoarseSourceTree` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.CoarseSourceTree.word` (the published bundle `Def_EditApproxScheme_12`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseBinaryBitWork.lean (declaration OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseBinaryEval_bitWork {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N R D A : ℕ) (frame : List (Option α)) (two : BinaryFraction)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (htwo : two.value = 2)
    (htw : two.width ≤ A) (hd : Nat.size two.representation.den ≤ D)
    (hroot : two.representation.den = coarseCommonDenominator 1 q L B R)
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hbound : Nat.size (coarseLevelMagnitude N k B R + 2) + 2 * D + 1 ≤ A)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction) (start : ℕ)
    (ha : CoarseGridCell two allowance k D A)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j)
    (hstart : start + tree.word.length ≤ N) :
    CoarseBinaryBox two (2 * k + 1) (coarseLevelMagnitude N k B d) D A
      (coarseBinaryEval k q L frame two tree draws allowance start).1 ∧
    (coarseBinaryEval k q L frame two tree draws allowance start).2 ≤
      (100000000 * (A + 1) ^ 2) * coarseBinaryWeight k q L tree draws allowance := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
