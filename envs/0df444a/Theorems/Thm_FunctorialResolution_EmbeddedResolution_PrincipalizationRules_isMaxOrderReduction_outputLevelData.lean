-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_isMaxOrderReduction_outputLevelData
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isMaxOrderReduction_outputLevelData
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:33:18.994653+00:00
-- url     : https://prove2.me/theorems/fb4a527c-5aa1-4794-821d-e2abdf35b7ae
-- title:
--   Principalization Rules: is Max Order Reduction output Level Data
-- statement:
--   The Principalization Rules construction uses the is Max Order Reduction output Level Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L181-L184

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isMaxOrderReduction_outputLevelData (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ) :
    IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed (B.outputLevelData n).orderRed := by sorry
