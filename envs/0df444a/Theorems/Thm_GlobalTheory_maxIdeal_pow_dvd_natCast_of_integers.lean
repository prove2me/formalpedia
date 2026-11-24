-- Prove2me | Theorems.Thm_GlobalTheory_maxIdeal_pow_dvd_natCast_of_integers
-- name    : GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:29.370255+00:00
-- url     : https://prove2.me/theorems/057f449e-b22b-497f-99b8-18ff56c3db14
-- title:
--   Global Theory: max Ideal pow dvd nat Cast of integers
-- statement:
--   The Global Theory construction uses the max Ideal pow dvd nat Cast of integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealPowNatCastDvdFiniteIntegersAlgebra.lean#L7-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealPowNatCastDvdFiniteIntegersAlgebra.lean#L7-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers :
    ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type)
      [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A]
      [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A →
      ∃ N : ℕ, (p : A) ∣ a ^ N := by sorry
