-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexInMoveToFront_self
-- name    : FunctorialResolution.EmbeddedResolution.indexInMoveToFront_self
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:36.894657+00:00
-- url     : https://prove2.me/theorems/616f45be-3eab-446f-92df-1f544bfe5d78
-- title:
--   Embedded Resolution: index In Move To Front self
-- statement:
--   The Embedded Resolution construction uses the index In Move To Front self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L88-L89

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

theorem FunctorialResolution.EmbeddedResolution.indexInMoveToFront_self (j : ℕ) : indexInMoveToFront j j = 0 := by sorry
