-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryRawCentersWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:28:28.515607+00:00
-- url     : https://prove2.me/theorems/dfc47526-67d7-4603-bb58-f6e85f1515aa
-- title:
--   OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryRawCenterCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRawCenterCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryRawCentersWithWork_bounds {n : ℕ} (N P F B : ℕ)
--       (a value : BinaryFraction) (q : TargetInterval n)
--       (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
--       (hP : 0 < P) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
--       (ha : a.width ≤ B) (hv : value.width ≤ B) :
--       (queryRawCentersWithWork N P F a value q).1.length ≤ (B + 1) * (64 * F * P + 2) ^ 2 ∧
--       (queryRawCentersWithWork N P F a value q).2 ≤ queryRawCentersBitBudget P F B
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryRawCentersBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork` (the published bundle `Def_EditApproxScheme_07`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryWarmupProgram_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryRawCenterCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryRawCentersWithWork_bounds {n : ℕ} (N P F B : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryRawCentersWithWork N P F a value q).1.length ≤ (B + 1) * (64 * F * P + 2) ^ 2 ∧
    (queryRawCentersWithWork N P F a value q).2 ≤ queryRawCentersBitBudget P F B := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
