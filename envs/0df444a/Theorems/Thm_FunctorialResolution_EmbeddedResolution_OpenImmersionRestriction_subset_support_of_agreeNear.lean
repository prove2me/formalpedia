-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_subset_support_of_agreeNear
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.subset_support_of_agreeNear
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:34.923569+00:00
-- url     : https://prove2.me/theorems/1fca5732-d679-4ec7-bc28-5a6d97abfeb4
-- title:
--   Open Immersion Restriction: subset support of agree Near
-- statement:
--   The Open Immersion Restriction construction uses the subset support of agree Near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean#L57-L63

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.subset_support_of_agreeNear {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (N : W.IdealSheafData) (T : Set ↥W) (hT : IsClosed T)
    (hagree : ∀ x ∈ T, AgreeNear N (V W ⟨T, hT⟩) x) :
    T ⊆ (N.support : Set ↥W) := by sorry
