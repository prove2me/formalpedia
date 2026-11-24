-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_mem_support_iff_of_agreeNear
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.mem_support_iff_of_agreeNear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:26.918808+00:00
-- url     : https://prove2.me/theorems/677bcab6-52f1-45bd-a72b-f204fb86bd52
-- title:
--   Open Immersion Restriction: mem support iff of agree Near
-- statement:
--   The Open Immersion Restriction construction uses the mem support iff of agree Near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L90-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L90-L104

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.mem_support_iff_of_agreeNear {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {W : Scheme.{u}} {I J : W.IdealSheafData} {x : ↥W} (h : AgreeNear I J x) :
    x ∈ (I.support : Set ↥W) ↔ x ∈ (J.support : Set ↥W) := by sorry
