-- Prove2me | Theorems.Thm_GlobalTheory_dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow
-- name    : GlobalTheory.dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:30.82524+00:00
-- url     : https://prove2.me/theorems/1d0431a5-79a8-4703-8ade-a6ba3ff10dfe
-- title:
--   Global Theory: dvr Subring eq pow mul nonmem of not mem pow
-- statement:
--   The Global Theory construction uses the dvr Subring eq pow mul nonmem of not mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrSubringEqTop.lean#L6-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrSubringEqTop.lean#L6-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) :
    ∀ N : ℕ, ∀ s ∈ S, s ∉ (IsLocalRing.maximalIdeal V) ^ N →
      ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by sorry
