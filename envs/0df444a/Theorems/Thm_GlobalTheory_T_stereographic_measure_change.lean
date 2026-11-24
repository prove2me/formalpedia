-- Prove2me | Theorems.Thm_GlobalTheory_T_stereographic_measure_change
-- name    : GlobalTheory.T.stereographic_measure_change
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:59:09.582076+00:00
-- url     : https://prove2.me/theorems/a684507c-f02b-4f21-9c7b-8a40c91b89ea
-- title:
--   T: stereographic measure change
-- statement:
--   The T construction uses the stereographic measure change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StereographicMeasureChangeStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StereographicMeasureChangeStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.stereographic_measure_change : ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by sorry
