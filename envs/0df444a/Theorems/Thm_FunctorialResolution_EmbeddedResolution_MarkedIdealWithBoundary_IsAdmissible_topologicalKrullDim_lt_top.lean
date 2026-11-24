-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_IsAdmissible_topologicalKrullDim_lt_top
-- name    : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.IsAdmissible.topologicalKrullDim_lt_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:04:37.189034+00:00
-- url     : https://prove2.me/theorems/cbaaa4ac-924b-4c4e-bd39-bb644aa4470f
-- title:
--   Is Admissible: topological Krull Dim lt top
-- statement:
--   The Is Admissible construction uses the topological Krull Dim lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L223-L225

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.IsAdmissible.topologicalKrullDim_lt_top {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) :
    topologicalKrullDim ↥T.scheme < ⊤ := by sorry
