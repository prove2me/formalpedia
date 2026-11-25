-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_liftDerivationOfKerEqSpan_apply
-- name    : FunctorialResolution.EmbeddedResolution.liftDerivationOfKerEqSpan_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:25.816462+00:00
-- url     : https://prove2.me/theorems/232985e8-31c8-42ca-8fbf-1ce2b194af2a
-- title:
--   Embedded Resolution: lift Derivation Of Ker Eq Span apply
-- statement:
--   The Embedded Resolution construction uses the lift Derivation Of Ker Eq Span apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/DerivationLiftAndDeterminant.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/DerivationLiftAndDeterminant.lean#L108-L112

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

theorem FunctorialResolution.EmbeddedResolution.liftDerivationOfKerEqSpan_apply (π : R →ₐ[k] S) (hπ : Function.Surjective π)
    (h : R) (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) (r : R) :
    liftDerivationOfKerEqSpan π hπ h hker D hD (π r) = π (D r) := by sorry
