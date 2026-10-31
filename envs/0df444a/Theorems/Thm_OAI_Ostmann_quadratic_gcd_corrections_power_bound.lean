-- Prove2me | Theorems.Thm_OAI_Ostmann_quadratic_gcd_corrections_power_bound
-- name    : OAI.Ostmann.quadratic_gcd_corrections_power_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:14:43.822853+00:00
-- url     : https://prove2.me/theorems/916a8844-a430-41a1-8283-694a9a1fd49e
-- title:
--   OAI.Ostmann.quadratic_gcd_corrections_power_bound: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.quadratic_gcd_corrections_power_bound` of [lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticGcdCorrectionPowerSaving.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticGcdCorrectionPowerSaving.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem quadratic_gcd_corrections_power_bound {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
--       (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
--       ∃ C : ℝ, 0 < C ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
--         (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
--           ‖quadraticGcdMomentCorrections M R K D (((M : ℝ) * R) ^ η) v‖ ≤
--             C * (D : ℝ) ^ 2 * ((M : ℝ) * R) ^ (36 * η) *
--               ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) * quadraticSieveEnergy (2 * R) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.QuadraticSieveGrowth` and `OAI.Ostmann.quadraticSieveEnergy` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.quadraticGcdMomentCorrections` (definitions bundle `OAIQ095D005` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.quadratic_rough_power_growth` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticGcdCorrectionPowerSaving.lean (declaration OAI.Ostmann.quadratic_gcd_corrections_power_bound)

import Mathlib
import Definitions.Def_OAIQ095D005

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_gcd_corrections_power_bound {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdMomentCorrections M R K D (((M : ℝ) * R) ^ η) v‖ ≤
          C * (D : ℝ) ^ 2 * ((M : ℝ) * R) ^ (36 * η) *
            ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) * quadraticSieveEnergy (2 * R) v := by
  sorry

end Ostmann

end OAI
end
