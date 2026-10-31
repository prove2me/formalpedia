-- Prove2me | Theorems.Thm_OAI_Ostmann_quadratic_first_total_growth
-- name    : OAI.Ostmann.quadratic_first_total_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:59.072983+00:00
-- url     : https://prove2.me/theorems/7124a8ff-5a52-48fd-8478-fab845ae3e87
-- title:
--   OAI.Ostmann.quadratic_first_total_growth: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.quadratic_first_total_growth` of [lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticFirstTotalGrowth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticFirstTotalGrowth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators ComplexConjugate`):
--
--   ```lean
--   theorem quadratic_first_total_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
--       (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
--       ∃ A : ℝ, 0 < A ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
--         ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
--           ‖∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
--             quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J‖ ≤
--           A * (2 * D : ℝ) * quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
--             ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
--               (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.QuadraticSieveGrowth` and `OAI.Ostmann.quadraticSieveEnergy` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.quadraticCorrectionScalar`, `OAI.Ostmann.quadraticGcdBlockSize`, `OAI.Ostmann.quadraticPairKernel` and `OAI.Ostmann.quadraticSecondWindow` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.quadraticFirstSecondCorrections` and `OAI.Ostmann.quadraticGcdPairs` (definitions bundle `OAIQ095D005` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.quadratic_gcd_corrections_power_bound` and `OAI_Ostmann_quadratic_rough_iteration` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticFirstTotalGrowth.lean (declaration OAI.Ostmann.quadratic_first_total_growth)

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

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_first_total_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
          quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J‖ ≤
        A * (2 * D : ℝ) * quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
          ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
            (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  sorry

end Ostmann

end OAI
end
