-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_outputLevelData_eq_nextLevel
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_eq_nextLevel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:31.616629+00:00
-- url     : https://prove2.me/theorems/e01cb373-16a7-5211-8d9c-067032d5dfc6
-- title:
--   Principalization Rules: output Level Data eq next Level
-- statement:
--   The Principalization Rules construction uses the output Level Data eq next Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L64-L65

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_eq_nextLevel (B : PrincipalizationRules.{u}) (n : ℕ) :
    B.outputLevelData n = B.nextLevel (B.inputLevelData n) := by sorry
