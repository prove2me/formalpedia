-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_npow_add
-- name    : GlobalTheory.Doubling.npow_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:40.145837+00:00
-- url     : https://prove2.me/theorems/f270d25a-d982-4dc7-affd-9c9eaa3109e5
-- title:
--   Doubling: npow add
-- statement:
--   The Doubling construction uses the npow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L112-L113

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

theorem GlobalTheory.Doubling.npow_add {r : ℝ≥0} (hr : 0 < r) (t t' : ℂ) : npow r (t + t') = npow r t * npow r t' := by sorry
