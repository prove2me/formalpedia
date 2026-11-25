-- Prove2me | Theorems.Thm_GlobalTheory_SS_projLinePlaces_X
-- name    : GlobalTheory.SS.projLinePlaces_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:30.217468+00:00
-- url     : https://prove2.me/theorems/a821910e-7b74-4f8b-85d4-dc753cf9a088
-- title:
--   SS: proj Line Places X
-- statement:
--   The SS construction uses the proj Line Places X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/PlOrdSomeOfAssociated.lean#L225-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/PlOrdSomeOfAssociated.lean#L225-L228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
open Polynomial IsDedekindDomain
variable (k : Type) [Field k]
variable {k}
variable (k)

theorem GlobalTheory.SS.projLinePlaces_X : (projLinePlaces k).v none (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = -1 := by sorry
