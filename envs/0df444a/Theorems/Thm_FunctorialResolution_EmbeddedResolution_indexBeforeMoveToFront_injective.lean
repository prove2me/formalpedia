-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexBeforeMoveToFront_injective
-- name    : FunctorialResolution.EmbeddedResolution.indexBeforeMoveToFront_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:03.097972+00:00
-- url     : https://prove2.me/theorems/066c839f-d315-49c5-badd-7dcaa64fcbe0
-- title:
--   Embedded Resolution: index Before Move To Front injective
-- statement:
--   The Embedded Resolution construction uses the index Before Move To Front injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L35-L53

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

theorem FunctorialResolution.EmbeddedResolution.indexBeforeMoveToFront_injective (j : ℕ) : Function.Injective (indexBeforeMoveToFront j) := by sorry
