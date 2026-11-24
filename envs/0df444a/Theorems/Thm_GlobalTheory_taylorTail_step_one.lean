-- Prove2me | Theorems.Thm_GlobalTheory_taylorTail_step_one
-- name    : GlobalTheory.taylorTail_step_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:35.372699+00:00
-- url     : https://prove2.me/theorems/de4433b1-ffdc-4129-a0af-bc2fb2ba5069
-- title:
--   Global Theory: taylor Tail step one
-- statement:
--   The Global Theory construction uses the taylor Tail step one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralTaylorTailIteratedDeriv.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralTaylorTailIteratedDeriv.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv
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
open GlobalTheory

theorem GlobalTheory.taylorTail_step_one {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (a : ℝ) (hg : Differentiable ℝ g) (hd : Continuous (deriv g))
    (hlim : Tendsto g atTop (𝓝 0)) :
    ENNReal.ofReal ‖g a‖ ≤ ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := by sorry
