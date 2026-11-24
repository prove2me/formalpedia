-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_inputLevelData_succ
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_succ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:34.368634+00:00
-- url     : https://prove2.me/theorems/35204980-2860-4beb-8497-dec871f472e8
-- title:
--   Principalization Rules: input Level Data succ
-- statement:
--   The Principalization Rules construction uses the input Level Data succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L67-L68

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_succ (B : PrincipalizationRules.{u}) (n : ℕ) :
    B.inputLevelData (n + 1) = B.outputLevelData n := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_succ
