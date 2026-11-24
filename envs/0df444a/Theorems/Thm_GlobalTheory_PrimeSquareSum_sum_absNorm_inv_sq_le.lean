-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSquareSum_sum_absNorm_inv_sq_le
-- name    : GlobalTheory.PrimeSquareSum.sum_absNorm_inv_sq_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:32.503306+00:00
-- url     : https://prove2.me/theorems/d545e623-5aea-4690-9258-465dad497f08
-- title:
--   Prime Square Sum: sum abs Norm inv sq le
-- statement:
--   The Prime Square Sum construction uses the sum abs Norm inv sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableAbsNormInvSq.lean#L28-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableAbsNormInvSq.lean#L28-L59

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

theorem GlobalTheory.PrimeSquareSum.sum_absNorm_inv_sq_le (K : Type) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ w ∈ s, (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by sorry
