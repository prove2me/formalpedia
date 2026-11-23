-- Prove2me | Theorems.Thm_GlobalTheory_Proof_sum_coset_reps_ne_zero_iff_commensurable_finsum_quot_eq
-- name    : GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:08.635435+00:00
-- url     : https://prove2.me/theorems/91aef6eb-7810-4dd1-bfd8-17e53bd4d6d8
-- title:
--   sum coset reps ne zero iff commensurable: finsum quot eq
-- statement:
--   The sum coset reps ne zero iff commensurable construction uses the finsum quot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumCosetRepsNeZeroIffCommensurable.lean#L5-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumCosetRepsNeZeroIffCommensurable.lean#L5-L64

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

theorem GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by sorry
