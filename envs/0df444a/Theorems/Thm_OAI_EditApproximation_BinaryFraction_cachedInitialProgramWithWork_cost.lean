-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_cachedInitialProgramWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:31.26319+00:00
-- url     : https://prove2.me/theorems/f2712f94-b001-4b82-afb9-dd54c7aff75b
-- title:
--   OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryCachedShellWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryCachedShellWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem cachedInitialProgramWithWork_cost {n : ℕ} (sourceLength N P F Amax B : ℕ)
--       (A a : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
--       (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
--       (hF : Nat.size F ≤ B) (hs : Nat.size sourceLength ≤ B) (hn : Nat.size n ≤ B)
--       (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B) (ha : a.width ≤ B)
--       (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
--       (cachedInitialProgramWithWork sourceLength N P F A a U q).2 ≤
--         cachedInitialProgramBitBudget P Amax B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.cachedInitialProgramBitBudget` and `OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryInitialConeProgramAt_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryCachedShellWork.lean (declaration OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace BinaryFraction

attribute [local irreducible] initialProgramWithWork localWarmupKernelWithWork

theorem cachedInitialProgramWithWork_cost {n : ℕ} (sourceLength N P F Amax B : ℕ)
    (A a : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F ≤ B) (hs : Nat.size sourceLength ≤ B) (hn : Nat.size n ≤ B)
    (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B) (ha : a.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
    (cachedInitialProgramWithWork sourceLength N P F A a U q).2 ≤
      cachedInitialProgramBitBudget P Amax B := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
