-- Prove2me | Theorems.Thm_GlobalTheory_SchemeWords_faithfullyFlat
-- name    : GlobalTheory.SchemeWords.faithfullyFlat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:31.957797+00:00
-- url     : https://prove2.me/theorems/926c886b-e90e-48d8-aa68-16fbb358dfa1
-- title:
--   Scheme Words: faithfully Flat
-- statement:
--   The Scheme Words construction uses the faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean#L47-L49

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
variable {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
  [Algebra A R] [IsLocalHom (algebraMap A R)]

theorem GlobalTheory.SchemeWords.faithfullyFlat (h : IsCompletedStrictHens A R) : Module.FaithfullyFlat A R := by sorry
