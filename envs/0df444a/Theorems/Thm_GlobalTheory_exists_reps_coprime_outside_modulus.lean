-- Prove2me | Theorems.Thm_GlobalTheory_exists_reps_coprime_outside_modulus
-- name    : GlobalTheory.exists_reps_coprime_outside_modulus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:28.057392+00:00
-- url     : https://prove2.me/theorems/05f7158a-177f-4858-a106-f6521ecf10c4
-- title:
--   Global Theory: exists reps coprime outside modulus
-- statement:
--   The Global Theory construction uses the exists reps coprime outside modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRepsCoprimeOutsideModulus.lean#L7-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRepsCoprimeOutsideModulus.lean#L7-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepsCoprimeOutsideModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDedekindDomain

theorem GlobalTheory.exists_reps_coprime_outside_modulus : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (m : Ideal A) (a₀ b₀ : A), m ≠ ⊥ → ∃ a b : A, a - a₀ ∈ m ∧ b - b₀ ∈ m ∧ b ≠ 0 ∧ ∀ p : Ideal A, p.IsMaximal → ¬ m ≤ p → ¬ (a ∈ p ∧ b ∈ p) := by sorry
