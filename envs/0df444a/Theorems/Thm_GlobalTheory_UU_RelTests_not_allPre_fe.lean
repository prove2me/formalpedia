-- Prove2me | Theorems.Thm_GlobalTheory_UU_RelTests_not_allPre_fe
-- name    : GlobalTheory.UU.RelTests.not_allPre_fe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:05.324362+00:00
-- url     : https://prove2.me/theorems/6b135b7d-4d98-437e-a9e3-b79650b82793
-- title:
--   Rel Tests: not all Pre fe
-- statement:
--   The Rel Tests construction uses the not all Pre fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/FinExtHomInjective.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/FinExtHomInjective.lean#L38-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_FinExtHomInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelTests

theorem GlobalTheory.UU.RelTests.not_allPre_fe : ¬ AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => U.FE (FractionRing V) 2 := by sorry
