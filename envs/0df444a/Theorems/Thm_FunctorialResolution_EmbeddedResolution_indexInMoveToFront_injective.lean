-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexInMoveToFront_injective
-- name    : FunctorialResolution.EmbeddedResolution.indexInMoveToFront_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:15.826384+00:00
-- url     : https://prove2.me/theorems/8e9918e1-53d6-4c41-b5a8-a1da1499fe32
-- title:
--   Embedded Resolution: index In Move To Front injective
-- statement:
--   The Embedded Resolution construction uses the index In Move To Front injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L91-L94

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

theorem FunctorialResolution.EmbeddedResolution.indexInMoveToFront_injective (j : ℕ) : Function.Injective (indexInMoveToFront j) := by sorry
