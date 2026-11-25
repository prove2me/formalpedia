-- Prove2me | Theorems.Thm_GlobalTheory_SchemeWords_finiteType_of_isQProjOver
-- name    : GlobalTheory.SchemeWords.finiteType_of_isQProjOver
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:22:17.882793+00:00
-- url     : https://prove2.me/theorems/42d7cdbe-662b-45da-aaff-843737512dfc
-- title:
--   Scheme Words: finite Type of is QProj Over
-- statement:
--   The Scheme Words construction uses the finite Type of is QProj Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L25-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SchemeWords
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}

theorem GlobalTheory.SchemeWords.finiteType_of_isQProjOver (h : IsQProjOver f) :
    LocallyOfFiniteType f ∧ QuasiCompact f ∧ IsSeparated f := by sorry
