-- Prove2me | Theorems.Thm_OAI_EditApproximation_unskipped_expected_regret_budget
-- name    : OAI.EditApproximation.unskipped_expected_regret_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:53.614328+00:00
-- url     : https://prove2.me/theorems/1bd1cf38-1481-4c99-a479-10209f1b2fe0
-- title:
--   OAI.EditApproximation.unskipped_expected_regret_budget: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.unskipped_expected_regret_budget` of [lean/OAI/Combinatorics/EditApproximation/Geometry/UnskippedRegretBudget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/UnskippedRegretBudget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--   theorem unskipped_expected_regret_budget {α : Type*} (source target : List α)
--       (N : ℕ) (hN : 0 < N) (hell : 42 ≤ inputSmallLog N) {M b P thetaExponent : ℕ}
--       (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
--       (parent : TargetInterval source.length) (tau F : ℚ)
--       (child initial : Fin M → TargetInterval target.length → ℚ)
--       (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
--       (hF : 0 ≤ F) (c : ℝ) (hb : (b : ℝ) ≤ c)
--       (eta kappa delta : ℚ) (heta : 0 < eta) (hkappa : 0 ≤ kappa) (S H : ℕ) :
--       ((∑ i, member.envelope i : ℚ) : ℝ) *
--           (Real.log (bandCoordinates member.actions.toFinset).card / (eta : ℝ) + 2 * (kappa : ℝ) +
--             (S : ℝ) / (H : ℝ) ^ 3) + 2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c ≤
--         (64 * (F : ℝ) *
--           ((4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (eta : ℝ) +
--             2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3) +
--           2 * (delta : ℝ) + 2 * S * (1 / (H : ℝ) ^ 4) * F) * c
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.bandCoordinates` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.instDecidableEqTargetInterval` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.UnskippedBand.actions` and `OAI.EditApproximation.UnskippedBand.envelope` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_global_node_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/UnskippedRegretBudget.lean (declaration OAI.EditApproximation.unskipped_expected_regret_budget)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

theorem unskipped_expected_regret_budget {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 42 ≤ inputSmallLog N) {M b P thetaExponent : ℕ}
    (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
    (parent : TargetInterval source.length) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hF : 0 ≤ F) (c : ℝ) (hb : (b : ℝ) ≤ c)
    (eta kappa delta : ℚ) (heta : 0 < eta) (hkappa : 0 ≤ kappa) (S H : ℕ) :
    ((∑ i, member.envelope i : ℚ) : ℝ) *
        (Real.log (bandCoordinates member.actions.toFinset).card / (eta : ℝ) + 2 * (kappa : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) + 2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c ≤
      (64 * (F : ℝ) *
        ((4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (eta : ℝ) +
          2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) + 2 * S * (1 / (H : ℝ) ^ 4) * F) * c := by
  sorry

end EditApproximation

end OAI
end
