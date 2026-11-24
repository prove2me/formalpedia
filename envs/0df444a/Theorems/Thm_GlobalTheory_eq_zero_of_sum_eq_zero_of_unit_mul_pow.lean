-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_sum_eq_zero_of_unit_mul_pow
-- name    : GlobalTheory.eq_zero_of_sum_eq_zero_of_unit_mul_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:18:40.234562+00:00
-- url     : https://prove2.me/theorems/d44cb41d-5526-4472-a40c-8425a2257772
-- title:
--   Global Theory: eq zero of sum eq zero of unit mul pow
-- statement:
--   The Global Theory construction uses the eq zero of sum eq zero of unit mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationLeCardOfSpan.lean#L5-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationLeCardOfSpan.lean#L5-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.eq_zero_of_sum_eq_zero_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by sorry
