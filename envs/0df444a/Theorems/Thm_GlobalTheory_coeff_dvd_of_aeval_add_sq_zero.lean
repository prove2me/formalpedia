-- Prove2me | Theorems.Thm_GlobalTheory_coeff_dvd_of_aeval_add_sq_zero
-- name    : GlobalTheory.coeff_dvd_of_aeval_add_sq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:57.256146+00:00
-- url     : https://prove2.me/theorems/705e43ba-0e02-44d5-9bc6-e8f7412cbe4a
-- title:
--   Global Theory: coeff dvd of aeval add sq zero
-- statement:
--   The Global Theory construction uses the coeff dvd of aeval add sq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffDvdOfAevalAddSqZero.lean#L70-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffDvdOfAevalAddSqZero.lean#L70-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffDvdOfAevalAddSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory

theorem GlobalTheory.coeff_dvd_of_aeval_add_sq_zero :
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, MvPolynomial.coeff m G = p * r) := by sorry
