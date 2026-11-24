-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_of_mem_moveToFront
-- name    : FunctorialResolution.EmbeddedResolution.mem_of_mem_moveToFront
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:48:03.376359+00:00
-- url     : https://prove2.me/theorems/7a6dea13-0baa-4b74-b740-9bcc8582c97e
-- title:
--   Embedded Resolution: mem of mem move To Front
-- statement:
--   The Embedded Resolution construction uses the mem of mem move To Front property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean#L119-L125

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

theorem FunctorialResolution.EmbeddedResolution.mem_of_mem_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) (D : α)
    (hD : D ∈ moveToFront E j) : D ∈ E := by sorry
