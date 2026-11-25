-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_outputLevelData_maxOrderReduction_eq_at_dim
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_maxOrderReduction_eq_at_dim
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:45.826011+00:00
-- url     : https://prove2.me/theorems/6f0abb71-879c-44c5-b145-61a92d905bb9
-- title:
--   Principalization Rules: output Level Data max Order Reduction eq at dim
-- statement:
--   The Principalization Rules construction uses the output Level Data max Order Reduction eq at dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L192-L195

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_maxOrderReduction_eq_at_dim (B : PrincipalizationRules.{u}) (T : MarkedIdealWithBoundary.{u}) {N : ℕ}
    (hT : T.krullDimSucc ≤ N) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData T.krullDimSucc).maxOrderRed T := by sorry
