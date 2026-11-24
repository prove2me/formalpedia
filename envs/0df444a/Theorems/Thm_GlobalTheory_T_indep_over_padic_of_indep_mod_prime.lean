-- Prove2me | Theorems.Thm_GlobalTheory_T_indep_over_padic_of_indep_mod_prime
-- name    : GlobalTheory.T.indep_over_padic_of_indep_mod_prime
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:54.47326+00:00
-- url     : https://prove2.me/theorems/c4883718-7e51-48a5-87ce-06fb378f1fff
-- title:
--   T: indep over padic of indep mod prime
-- statement:
--   The T construction uses the indep over padic of indep mod prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOverPadicOfIndepModPrimeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOverPadicOfIndepModPrimeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOverPadicOfIndepModPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOverPadicOfIndepModPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.indep_over_padic_of_indep_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by sorry
