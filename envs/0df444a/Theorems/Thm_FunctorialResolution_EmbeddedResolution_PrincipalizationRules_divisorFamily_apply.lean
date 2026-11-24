-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_divisorFamily_apply
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationRules.divisorFamily_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:33:50.587811+00:00
-- url     : https://prove2.me/theorems/fae0b04c-d862-4639-a112-0a794003c862
-- title:
--   Principalization Rules: divisor Family apply
-- statement:
--   The Principalization Rules construction uses the divisor Family apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean#L24-L26

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

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationRules.divisorFamily_apply (B : PrincipalizationRules.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) :
    B.divisorFamily L j T = B.divisorRed T (fun S _ => L S) j := by sorry
