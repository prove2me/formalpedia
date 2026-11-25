-- Prove2me | Theorems.Thm_GlobalTheory_FlatChecks_coord_differentiableAt
-- name    : GlobalTheory.FlatChecks.coord_differentiableAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:26.565133+00:00
-- url     : https://prove2.me/theorems/5256164e-3148-5c41-bdc7-672974f84b75
-- title:
--   Flat Checks: coord differentiable At
-- statement:
--   The Flat Checks construction uses the coord differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L47-L58

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

theorem GlobalTheory.FlatChecks.coord_differentiableAt (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (j : Fin Fl.δ) :
    DifferentiableAt ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) 0 := by sorry
