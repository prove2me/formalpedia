-- Prove2me | Theorems.Thm_GlobalTheory_Proof_sum_coset_reps_ne_zero_iff_commensurable_sum_reps_ne_zero_iff
-- name    : GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:20.289805+00:00
-- url     : https://prove2.me/theorems/67667353-8e62-45c5-acdd-a3a1c454fb16
-- title:
--   sum coset reps ne zero iff commensurable: sum reps ne zero iff
-- statement:
--   The sum coset reps ne zero iff commensurable construction uses the sum reps ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumCosetRepsNeZeroIffCommensurable.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumCosetRepsNeZeroIffCommensurable.lean#L66-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumCosetRepsNeZeroIffCommensurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable

theorem GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by sorry
