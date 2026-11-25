-- Prove2me | Theorems.Thm_GlobalTheory_T_ae_transcendental_point_nonvanishing
-- name    : GlobalTheory.T.ae_transcendental_point_nonvanishing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:12.27769+00:00
-- url     : https://prove2.me/theorems/6ea74878-2a50-50c8-9f94-895e4116d729
-- title:
--   T: ae transcendental point nonvanishing
-- statement:
--   The T construction uses the ae transcendental point nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AeTranscendentalPointNonvanishingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AeTranscendentalPointNonvanishingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AeTranscendentalPointNonvanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AeTranscendentalPointNonvanishingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ae_transcendental_point_nonvanishing : ∀ (K : Type) [Field K] [Countable K] (σ : K →+* ℂ) (ι : Type) [Fintype ι], ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by sorry
