-- Prove2me | Theorems.Thm_GlobalTheory_T_maximalIdeal_pow_natCast_dvd_finite_integers_algebra
-- name    : GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:17.674072+00:00
-- url     : https://prove2.me/theorems/be45e412-8576-4860-ad74-45c188dfd0ab
-- title:
--   T: maximal Ideal pow nat Cast dvd finite integers algebra
-- statement:
--   The T construction uses the maximal Ideal pow nat Cast dvd finite integers algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealPowNatCastDvdFiniteIntegersAlgebraStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealPowNatCastDvdFiniteIntegersAlgebraStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealPowNatCastDvdFiniteIntegersAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra : ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A → ∃ N : ℕ, (p : A) ∣ a ^ N := by sorry
