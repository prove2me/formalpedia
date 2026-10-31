-- Prove2me | Theorems.Thm_OAI_Ostmann_quadratic_gcd_main_growth
-- name    : OAI.Ostmann.quadratic_gcd_main_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:17:42.231655+00:00
-- url     : https://prove2.me/theorems/a3563f57-76e2-4761-9505-5ae2b5a202c0
-- title:
--   OAI.Ostmann.quadratic_gcd_main_growth: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.quadratic_gcd_main_growth` of [lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticGcdMainGrowth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticGcdMainGrowth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem quadratic_gcd_main_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ C : ℝ, 0 < C ∧ ∀ M N D K : ℕ, 0 < M → 0 < N →
--         Squarefree D → Odd D → 0 < K → ∀ v : ℕ → ℂ,
--         ‖quadraticTransformedFirstMain M N D K quadraticSieveWeight v -
--           quadraticSmallTransformedMain M N D K quadraticSieveWeight v‖ ≤
--           C * (((K * D ^ 2 : ℕ) : ℝ) * N) ^ (2 * ε) * (D : ℝ) ^ ε *
--             (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + N) *
--               quadraticSieveEnergy N v
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.QuadraticSieveGrowth` and `OAI.Ostmann.quadraticSieveEnergy` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.quadraticSieveWeight`, `OAI.Ostmann.quadraticSmallTransformedMain` and `OAI.Ostmann.quadraticTransformedFirstMain` (definitions bundle `OAIQ095D005` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.quadratic_rough_power_growth` and `OAI_Ostmann_quadratic_small_gcd_comparison` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticGcdMainGrowth.lean (declaration OAI.Ostmann.quadratic_gcd_main_growth)

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

theorem quadratic_gcd_main_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N D K : ℕ, 0 < M → 0 < N →
      Squarefree D → Odd D → 0 < K → ∀ v : ℕ → ℂ,
      ‖quadraticTransformedFirstMain M N D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M N D K quadraticSieveWeight v‖ ≤
        C * (((K * D ^ 2 : ℕ) : ℝ) * N) ^ (2 * ε) * (D : ℝ) ^ ε *
          (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + N) *
            quadraticSieveEnergy N v := by
  sorry

end Ostmann

end OAI
end
