-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_inputLevelData_zero
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:10.830428+00:00
-- url     : https://prove2.me/theorems/16ac1998-b0b9-4a05-9355-f52a7c1dfb0a
-- title:
--   Principalization Rules: input Level Data zero
-- statement:
--   The Principalization Rules construction uses the input Level Data zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L61-L62

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_zero (B : PrincipalizationRules.{u}) :
    B.inputLevelData 0 = trivialOrderReductionData.{u} := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_zero
