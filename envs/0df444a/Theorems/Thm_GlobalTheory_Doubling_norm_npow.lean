-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_norm_npow
-- name    : GlobalTheory.Doubling.norm_npow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:42.817195+00:00
-- url     : https://prove2.me/theorems/4bd6b6ea-a374-4fc0-87ad-11b735965630
-- title:
--   Doubling: norm npow
-- statement:
--   The Doubling construction uses the norm npow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L118-L119

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

theorem GlobalTheory.Doubling.norm_npow {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : ‖npow r t‖ = (r : ℝ) ^ t.re := by sorry
