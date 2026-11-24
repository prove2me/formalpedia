-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_nodup_sum_multiset_of_eq
-- name    : GlobalTheory.eq_of_nodup_sum_multiset_of_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:20.190885+00:00
-- url     : https://prove2.me/theorems/3e4568b8-05cf-4056-bdcc-124f2414aff1
-- title:
--   Global Theory: eq of nodup sum multiset of eq
-- statement:
--   The Global Theory construction uses the eq of nodup sum multiset of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqOfNodupSumMultisetOfEq.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqOfNodupSumMultisetOfEq.lean#L5-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqOfNodupSumMultisetOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by sorry
