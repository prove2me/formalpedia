-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_maxOrderFamily_apply
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.maxOrderFamily_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:43.539237+00:00
-- url     : https://prove2.me/theorems/7379ac72-3344-4241-ad12-515b8aa45ac0
-- title:
--   Principalization Rules: max Order Family apply
-- statement:
--   The Principalization Rules construction uses the max Order Family apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L40-L42

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PrincipalizationRules

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.maxOrderFamily_apply (B : PrincipalizationRules.{u}) (A : PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    B.maxOrderFamily A T = B.maxOrderRed T (fun S _ => A S) := by sorry
