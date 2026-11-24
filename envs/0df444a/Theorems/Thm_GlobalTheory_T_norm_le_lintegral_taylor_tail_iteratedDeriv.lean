-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_le_lintegral_taylor_tail_iteratedDeriv
-- name    : GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:52.171878+00:00
-- url     : https://prove2.me/theorems/303bf73d-d32f-45cc-8178-a5a89ce8e29e
-- title:
--   T: norm le lintegral taylor tail iterated Deriv
-- statement:
--   The T construction uses the norm le lintegral taylor tail iterated Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralTaylorTailIteratedDerivStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralTaylorTailIteratedDerivStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDerivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (h : ℝ → F) (m : ℕ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) → ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by sorry
