-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_sum_divisors_prime_mul
-- name    : GlobalTheory.QuadraticZeta.sum_divisors_prime_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:29.313395+00:00
-- url     : https://prove2.me/theorems/31c21a02-ef18-4738-9d3c-f1d813f846e2
-- title:
--   Quadratic Zeta: sum divisors prime mul
-- statement:
--   The Quadratic Zeta construction uses the sum divisors prime mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L316-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L316-L351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.QuadraticZeta.sum_divisors_prime_mul {R : Type*} [CommRing R] (χ : ℕ → R)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    ∑ e ∈ (p * m).divisors, χ e = (1 + χ p) * ∑ e ∈ m.divisors, χ e
      - χ p * if p ∣ m then ∑ e ∈ (m / p).divisors, χ e else 0 := by sorry
