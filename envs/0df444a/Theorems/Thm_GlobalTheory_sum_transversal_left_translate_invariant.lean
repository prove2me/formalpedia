-- Prove2me | Theorems.Thm_GlobalTheory_sum_transversal_left_translate_invariant
-- name    : GlobalTheory.sum_transversal_left_translate_invariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:14.450515+00:00
-- url     : https://prove2.me/theorems/f0e9e152-98d7-434f-93c1-d5be3115a13a
-- title:
--   Global Theory: sum transversal left translate invariant
-- statement:
--   The Global Theory construction uses the sum transversal left translate invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTransversalLeftTranslateInvariant.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTransversalLeftTranslateInvariant.lean#L5-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTransversalLeftTranslateInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.sum_transversal_left_translate_invariant :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by sorry
