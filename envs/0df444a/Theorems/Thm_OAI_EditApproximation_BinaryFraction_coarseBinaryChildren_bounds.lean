-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_coarseBinaryChildren_bounds
-- name    : OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:09.359558+00:00
-- url     : https://prove2.me/theorems/5a3167e1-4f7a-49a6-9ce8-3ff080c90cc1
-- title:
--   OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds` of [lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseChildrenBitWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseChildrenBitWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--    theorem coarseBinaryChildren_bounds {B d : ℕ} {α : Type*} (k q L N V D A : ℕ)
--       (two allowance : BinaryFraction)
--       (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
--         CoarseBinaryArray × ℕ)
--       (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
--       (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
--       (hB : 0 < B) (hlen : children.length ≤ B) (htwo : two.value = 2) (htw : two.width ≤ A)
--       (ha : allowance.width ≤ A) (hBbits : Nat.size B + 2 ≤ A)
--       (hqbits : Nat.size q + 2 ≤ A) (hLbits : Nat.size L + 2 ≤ A)
--       (hNbits : Nat.size N ≤ A)
--       (ht : ∀ draw : Fin B, (coarseChildThresholdWithWork B q allowance draw).1.width ≤ A)
--       (hs : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A)
--       (hbound : Nat.size (B * (V + k) + 2) + 2 * D + 1 ≤ A)
--       (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ s,
--         s + child.word.length ≤ N →
--         CoarseBinaryBox two (2 * k + 1) V D A
--           (evaluate child below (coarseChildAllowanceWithWork L
--             (coarseChildThresholdWithWork B q allowance draw).1).1 s).1 ∧
--         (evaluate child below (coarseChildAllowanceWithWork L
--             (coarseChildThresholdWithWork B q allowance draw).1).1 s).2 ≤
--           (100000000 * (A + 1) ^ 2) * weight child below
--             (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1)
--       (start : ℕ) (hstart : start + coarseChildrenSpan children ≤ N) :
--       CoarseBinaryBox two (2 * k + 1) (children.length * (V + k)) D A
--         (coarseBinaryChildren k q L two evaluate allowance children start).1 ∧
--       (coarseBinaryChildren k q L two evaluate allowance children start).2 + children.length ≤
--         (100000000 * (A + 1) ^ 2) *
--           (coarseBinaryChildrenWeight q L weight allowance children + (2 * k + 1) * children.length)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.CoarseBinaryBox`, `OAI.EditApproximation.BinaryFraction.CoarseGridCell`, `OAI.EditApproximation.BinaryFraction.coarseBinaryChildren`, `OAI.EditApproximation.BinaryFraction.coarseBinaryChildrenWeight` and `OAI.EditApproximation.BinaryFraction.coarseChildrenSpan` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.CoarseBinaryArray` and `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.coarseChildAllowanceWithWork`, `OAI.EditApproximation.BinaryFraction.coarseChildThresholdWithWork` and `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.CoarseSourceTree` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.CoarseSourceTree.word` (the published bundle `Def_EditApproxScheme_12`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Coarse/CoarseChildrenBitWork.lean (declaration OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds)

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

 theorem coarseBinaryChildren_bounds {B d : ℕ} {α : Type*} (k q L N V D A : ℕ)
    (two allowance : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hB : 0 < B) (hlen : children.length ≤ B) (htwo : two.value = 2) (htw : two.width ≤ A)
    (ha : allowance.width ≤ A) (hBbits : Nat.size B + 2 ≤ A)
    (hqbits : Nat.size q + 2 ≤ A) (hLbits : Nat.size L + 2 ≤ A)
    (hNbits : Nat.size N ≤ A)
    (ht : ∀ draw : Fin B, (coarseChildThresholdWithWork B q allowance draw).1.width ≤ A)
    (hs : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A)
    (hbound : Nat.size (B * (V + k) + 2) + 2 * D + 1 ≤ A)
    (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ s,
      s + child.word.length ≤ N →
      CoarseBinaryBox two (2 * k + 1) V D A
        (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).1 ∧
      (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).2 ≤
        (100000000 * (A + 1) ^ 2) * weight child below
          (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1)
    (start : ℕ) (hstart : start + coarseChildrenSpan children ≤ N) :
    CoarseBinaryBox two (2 * k + 1) (children.length * (V + k)) D A
      (coarseBinaryChildren k q L two evaluate allowance children start).1 ∧
    (coarseBinaryChildren k q L two evaluate allowance children start).2 + children.length ≤
      (100000000 * (A + 1) ^ 2) *
        (coarseBinaryChildrenWeight q L weight allowance children + (2 * k + 1) * children.length) := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
