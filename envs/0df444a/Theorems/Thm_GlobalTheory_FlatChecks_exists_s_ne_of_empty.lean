-- Prove2me | Theorems.Thm_GlobalTheory_FlatChecks_exists_s_ne_of_empty
-- name    : GlobalTheory.FlatChecks.exists_s_ne_of_empty
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:44.348293+00:00
-- url     : https://prove2.me/theorems/8b7c005e-7373-45e8-9384-ad7120718cfe
-- title:
--   Flat Checks: exists s ne of empty
-- statement:
--   The Flat Checks construction uses the exists s ne of empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L60-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.FlatChecks.exists_s_ne_of_empty (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (h : Fl.δ = 0) :
    ∀ x ∈ X.dom, ∃ k, Fl.s k x ≠ 0 := by sorry
