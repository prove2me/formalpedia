-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_npow_ne_zero
-- name    : GlobalTheory.Doubling.npow_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:21.095347+00:00
-- url     : https://prove2.me/theorems/d52b9f07-cc92-45ff-86be-215329f5ee48
-- title:
--   Doubling: npow ne zero
-- statement:
--   The Doubling construction uses the npow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L121-L122

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory

theorem GlobalTheory.Doubling.npow_ne_zero {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t ≠ 0 := by sorry
