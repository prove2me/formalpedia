-- Prove2me | Theorems.Thm_OAI_Ostmann_quadratic_rough_power_growth
-- name    : OAI.Ostmann.quadratic_rough_power_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:02:58.732128+00:00
-- url     : https://prove2.me/theorems/2aac77f9-82bd-4000-88e6-499ea7e64bcf
-- title:
--   OAI.Ostmann.quadratic_rough_power_growth: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.quadratic_rough_power_growth` of [lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticRoughPowerGrowth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticRoughPowerGrowth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`):
--
--   ```lean
--   theorem quadratic_rough_power_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
--       (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
--       ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ,
--         0 < M → 0 < N → 0 < K → K ≤ M →
--         2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
--         QuadraticRoughBound M N K
--           (C * ((M : ℝ) * N) ^ ε * quadraticDescentScale ξ M N K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.QuadraticRoughBound` and `OAI.Ostmann.QuadraticSieveGrowth` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.quadraticDescentScale` (definitions bundle `OAIQ095D002` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.publishedQuadraticLargeSieve` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticRoughPowerGrowth.lean (declaration OAI.Ostmann.quadratic_rough_power_growth)

import Mathlib
import Definitions.Def_OAIQ095D001
import Definitions.Def_OAIQ095D002

section

attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

theorem quadratic_rough_power_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ,
      0 < M → 0 < N → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        (C * ((M : ℝ) * N) ^ ε * quadraticDescentScale ξ M N K) := by
  sorry

end Ostmann

end OAI
end
