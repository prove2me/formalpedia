-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_isOrderReduction_outputLevelData
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isOrderReduction_outputLevelData
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:33:45.657095+00:00
-- url     : https://prove2.me/theorems/f2674245-e2cb-41c4-8a5e-f7eb2d012403
-- title:
--   Principalization Rules: is Order Reduction output Level Data
-- statement:
--   The Principalization Rules construction uses the is Order Reduction output Level Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L171-L179

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isOrderReduction_outputLevelData (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ) :
    IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed := by sorry
