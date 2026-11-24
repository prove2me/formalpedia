-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_npow_eq_exp
-- name    : GlobalTheory.Doubling.npow_eq_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:14.263816+00:00
-- url     : https://prove2.me/theorems/991ae0e5-264e-419b-97e7-6bbe8396b6e1
-- title:
--   Doubling: npow eq exp
-- statement:
--   The Doubling construction uses the npow eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L124-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L124-L125

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

theorem GlobalTheory.Doubling.npow_eq_exp {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t = Complex.exp (Real.log r * t) := by sorry
