-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_nextLevel_orderReduction
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_orderReduction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:50.278806+00:00
-- url     : https://prove2.me/theorems/d552db16-3f1c-4cb1-861e-3248b770b9bb
-- title:
--   Principalization Rules: next Level order Reduction
-- statement:
--   The Principalization Rules construction uses the next Level order Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L48-L49

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_orderReduction (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) :
    (B.nextLevel L).orderRed = B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_orderReduction
