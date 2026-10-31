-- Prove2me | Theorems.Thm_OAI_Ostmann_quadratic_full_middle_growth
-- name    : OAI.Ostmann.quadratic_full_middle_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:15:25.599042+00:00
-- url     : https://prove2.me/theorems/9aedbadd-4b0f-4445-86de-537e078e34f9
-- title:
--   OAI.Ostmann.quadratic_full_middle_growth: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.quadratic_full_middle_growth` of [lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticFullMiddleGrowth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticFullMiddleGrowth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem quadratic_full_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
--       ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M H J : ℝ,
--         0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ e N Q K L : ℕ,
--         0 < M → 0 < H → (N : ℝ) ≤ 2 * H → 0 < e →
--         0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
--         ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
--         (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
--         (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
--           QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
--             (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
--         ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
--             quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤
--           ((Nat.log 2 K + 1 : ℕ) : ℝ) *
--             ((128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
--               (10 * C * (4 * (K : ℝ) * N) ^ ε *
--                 (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
--                   (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
--                     Real.sqrt (quadraticDivisorMoment (2 * N) w)))) *
--                       (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.QuadraticSieveBound` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.quadraticGrowthCutoff` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.quadraticDivisorMoment` and `OAI.Ostmann.quadraticFullMiddleCorrection` (definitions bundle `OAIQ095D005` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.quadratic_first_total_growth` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/QuadraticFullMiddleGrowth.lean (declaration OAI.Ostmann.quadratic_full_middle_growth)

import Mathlib
import Definitions.Def_OAIQ095D005

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_full_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M H J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ e N Q K L : ℕ,
      0 < M → 0 < H → (N : ℝ) ≤ 2 * H → 0 < e →
      0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤
        ((Nat.log 2 K + 1 : ℕ) : ℝ) *
          ((128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
            (10 * C * (4 * (K : ℝ) * N) ^ ε *
              (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
                (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                  Real.sqrt (quadraticDivisorMoment (2 * N) w)))) *
                    (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb)) := by
  sorry

end Ostmann

end OAI
end
