-- Prove2me | Theorems.Thm_GlobalTheory_SchemeWords_isProper_of_isProjOver
-- name    : GlobalTheory.SchemeWords.isProper_of_isProjOver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:46.443682+00:00
-- url     : https://prove2.me/theorems/adb0dfe2-6d88-4809-a4ef-ffed8faf4f87
-- title:
--   Scheme Words: is Proper of is Proj Over
-- statement:
--   The Scheme Words construction uses the is Proper of is Proj Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L16-L17

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

theorem GlobalTheory.SchemeWords.isProper_of_isProjOver (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : IsProper f := by sorry
