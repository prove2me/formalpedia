-- Prove2me | Theorems.Thm_GlobalTheory_SchemeWords_isQProjOver_of_isProjOver
-- name    : GlobalTheory.SchemeWords.isQProjOver_of_isProjOver
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:00.423587+00:00
-- url     : https://prove2.me/theorems/eee55a6c-09e1-46ff-aab2-8fbe14badb1c
-- title:
--   Scheme Words: is QProj Over of is Proj Over
-- statement:
--   The Scheme Words construction uses the is QProj Over of is Proj Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L21-L23

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
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}

theorem GlobalTheory.SchemeWords.isQProjOver_of_isProjOver (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f := by sorry
