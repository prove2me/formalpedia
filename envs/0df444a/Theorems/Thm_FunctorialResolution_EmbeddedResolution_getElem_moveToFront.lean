-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_getElem_moveToFront
-- name    : FunctorialResolution.EmbeddedResolution.getElem_moveToFront
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:37.996803+00:00
-- url     : https://prove2.me/theorems/9ba18052-6fd6-4b51-ad1d-99e53b5ac2de
-- title:
--   Embedded Resolution: get Elem move To Front
-- statement:
--   The Embedded Resolution construction uses the get Elem move To Front property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L63-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L63-L84

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*}

theorem FunctorialResolution.EmbeddedResolution.getElem_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
    (hi : i < (moveToFront E j).length) :
    (moveToFront E j)[i]'hi =
      E[indexBeforeMoveToFront j i]'(indexBeforeMoveToFront_lt_length E j hj i (by
        rw [length_moveToFront E j hj] at hi; exact hi)) := by sorry
