-- Prove2me | Theorems.Thm_GlobalTheory_DegActCheck_pt_zero
-- name    : GlobalTheory.DegActCheck.pt_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:34.643817+00:00
-- url     : https://prove2.me/theorems/551f0dd4-b289-4700-bdba-5c486cbd7ceb
-- title:
--   Deg Act Check: pt zero
-- statement:
--   The Deg Act Check construction uses the pt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/PsiUnitOnIffInterior.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/PsiUnitOnIffInterior.lean#L72-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_PsiUnitOnIffInterior
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R]
variable {O : Type} [CommRing O] [StarRing O] (D : Out.DegPre R) [Module O D.X] (oa : D.OAct O) (w : O) (y : D.X)

theorem GlobalTheory.DegActCheck.pt_zero : D.xK y ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit (Out.TK R)).left ≫ eSec D.P.A := by sorry
