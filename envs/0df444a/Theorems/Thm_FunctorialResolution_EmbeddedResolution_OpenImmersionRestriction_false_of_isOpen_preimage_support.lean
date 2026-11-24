-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_false_of_isOpen_preimage_support
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.false_of_isOpen_preimage_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:31.612905+00:00
-- url     : https://prove2.me/theorems/2ff4399d-66b9-48a9-9c37-cf40dd8a49d0
-- title:
--   Open Immersion Restriction: false of is Open preimage support
-- statement:
--   The Open Immersion Restriction construction uses the false of is Open preimage support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L161-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean#L161-L208

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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.false_of_isOpen_preimage_support {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (N Z : W.IdealSheafData) (C : IrreducibleClosedPair W) (U : W.Opens)
    (H : (U.toScheme).IdealSheafData)
    (hptU : C.pt ∈ (U : Set ↥W)) (hptZ : C.pt ∈ (Z.support : Set ↥W))
    (hZH : ((Z.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hNsubH : ((N.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hopen : IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme))))
    (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by sorry
