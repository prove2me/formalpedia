-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_nextLevel_maxOrderReduction
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_maxOrderReduction
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:50.612526+00:00
-- url     : https://prove2.me/theorems/82040231-e275-44c3-86c4-5c2e5887f8e6
-- title:
--   Principalization Rules: next Level max Order Reduction
-- statement:
--   The Principalization Rules construction uses the next Level max Order Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L51-L53

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_maxOrderReduction (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) :
    (B.nextLevel L).maxOrderRed =
      B.maxOrderFamily (B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j)) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_maxOrderReduction
