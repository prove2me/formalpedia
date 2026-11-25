-- Prove2me | Theorems.Thm_GlobalTheory_eLpNorm_two_le_of_lintegral
-- name    : GlobalTheory.eLpNorm_two_le_of_lintegral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:17.143104+00:00
-- url     : https://prove2.me/theorems/fecc9e90-0726-52f3-a6ad-a857b07e5f96
-- title:
--   Global Theory: e Lp Norm two le of lintegral
-- statement:
--   The Global Theory construction uses the e Lp Norm two le of lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtendAeLinearOfLocalSqBoundDense.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtendAeLinearOfLocalSqBoundDense.lean#L14-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtendAeLinearOfLocalSqBoundDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.eLpNorm_two_le_of_lintegral {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (g : Q → E) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm g 2 ν ≤ ENNReal.ofReal B := by sorry
