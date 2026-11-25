-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_outputLevelData_orderReduction_eq_orderFamily
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_orderReduction_eq_orderFamily
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:36.462061+00:00
-- url     : https://prove2.me/theorems/eed612d8-8ff1-49ee-9b71-fcf4577098fc
-- title:
--   Principalization Rules: output Level Data order Reduction eq order Family
-- statement:
--   The Principalization Rules construction uses the output Level Data order Reduction eq order Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L73-L74

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_orderReduction_eq_orderFamily (B : PrincipalizationRules.{u}) (n : ℕ) :
    (B.outputLevelData n).orderRed = B.orderFamily (fun j => B.levelDivisorFamily n j) := by sorry
