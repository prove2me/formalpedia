-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_npow_mul
-- name    : GlobalTheory.Doubling.npow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:42.017661+00:00
-- url     : https://prove2.me/theorems/1c8f88b7-6645-47cb-b38f-e87753a96690
-- title:
--   Doubling: npow mul
-- statement:
--   The Doubling construction uses the npow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L109-L110

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

theorem GlobalTheory.Doubling.npow_mul (r r' : ℝ≥0) (t : ℂ) : npow (r * r') t = npow r t * npow r' t := by sorry
