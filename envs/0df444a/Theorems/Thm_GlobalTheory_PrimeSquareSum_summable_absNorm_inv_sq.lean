-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSquareSum_summable_absNorm_inv_sq
-- name    : GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:00.380249+00:00
-- url     : https://prove2.me/theorems/3b8968bf-8afc-43c6-a482-b8bb223f2db8
-- title:
--   Prime Square Sum: summable abs Norm inv sq
-- statement:
--   The Prime Square Sum construction uses the summable abs Norm inv sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableAbsNormInvSq.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableAbsNormInvSq.lean#L61-L66

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

theorem GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq : ∀ (K : Type) [Field K] [NumberField K], Summable (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) ∧ ∑' w : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by sorry
