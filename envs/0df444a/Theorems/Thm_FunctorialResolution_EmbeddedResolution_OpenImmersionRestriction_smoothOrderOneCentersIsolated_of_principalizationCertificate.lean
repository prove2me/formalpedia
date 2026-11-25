-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_smoothOrderOneCentersIsolated_of_principalizationCertificate
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.smoothOrderOneCentersIsolated_of_principalizationCertificate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:58.570596+00:00
-- url     : https://prove2.me/theorems/96afa05c-d737-52d7-8884-5eb6715c4f63
-- title:
--   Open Immersion Restriction: smooth Order One Centers Isolated of principalization Certificate
-- statement:
--   The Open Immersion Restriction construction uses the smooth Order One Centers Isolated of principalization Certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean#L307-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean#L307-L360

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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.smoothOrderOneCentersIsolated_of_principalizationCertificate {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated V W p I m Mem Z := by sorry
