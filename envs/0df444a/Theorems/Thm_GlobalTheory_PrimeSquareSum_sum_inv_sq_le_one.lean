-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSquareSum_sum_inv_sq_le_one
-- name    : GlobalTheory.PrimeSquareSum.sum_inv_sq_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:05.441539+00:00
-- url     : https://prove2.me/theorems/a6bb3b6b-602c-4d06-9cf7-7f90d7fed226
-- title:
--   Prime Square Sum: sum inv sq le one
-- statement:
--   The Prime Square Sum construction uses the sum inv sq le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableAbsNormInvSq.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableAbsNormInvSq.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableAbsNormInvSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.PrimeSquareSum

theorem GlobalTheory.PrimeSquareSum.sum_inv_sq_le_one (t : Finset ℕ) (ht : ∀ n ∈ t, 2 ≤ n) :
    ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by sorry
