-- Prove2me | Theorems.Thm_OAI_Ostmann_densitySmoothedSquare_mean
-- name    : OAI.Ostmann.densitySmoothedSquare_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:07:50.631464+00:00
-- url     : https://prove2.me/theorems/2cee0e2b-93b9-402f-94c9-eca175f6d02c
-- title:
--   OAI.Ostmann.densitySmoothedSquare_mean: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.densitySmoothedSquare_mean` of [lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensitySmoothedMean.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensitySmoothedMean.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Complex MeasureTheory Filter Set`, `open scoped BigOperators Topology Classical`):
--
--   ```lean
--    theorem densitySmoothedSquare_mean :
--       ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ,
--         1 ≤ T → 1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N →
--         ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
--         (∀ χ ∈ F, Integrable (fun t =>
--           ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2)
--             (volume.restrict (Icc (-T) T))) ∧
--         (∑ χ ∈ F, ∫ t in Icc (-T) T,
--           ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
--             C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveComplexCharacter` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.densityVerticalPoint` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.densitySmoothedSquare` (definitions bundle `OAIQ095D004` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.density_packed_product_fourth` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensitySmoothedMean.lean (declaration OAI.Ostmann.densitySmoothedSquare_mean)

import Mathlib
import Definitions.Def_OAIQ095D004

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Complex MeasureTheory Filter Set
open scoped BigOperators Topology Classical

 theorem densitySmoothedSquare_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ,
      1 ≤ T → 1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∀ χ ∈ F, Integrable (fun t =>
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2)
          (volume.restrict (Icc (-T) T))) ∧
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  sorry

end Ostmann

end OAI
end
