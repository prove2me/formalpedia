-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_continuous_npow
-- name    : GlobalTheory.Doubling.continuous_npow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:46.813753+00:00
-- url     : https://prove2.me/theorems/ba89cc16-ed6b-4f22-9785-287a064e8b12
-- title:
--   Doubling: continuous npow
-- statement:
--   The Doubling construction uses the continuous npow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L127-L131

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

theorem GlobalTheory.Doubling.continuous_npow {X : Type} [TopologicalSpace X] {f : X → ℝ≥0} (hf : Continuous f) (h : ∀ x, 0 < f x) (t : ℂ) :
    Continuous fun x => npow (f x) t := by sorry
