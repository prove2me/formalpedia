-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_preimage_basicOpen_specToAffineSpaceExtendCoords
-- name    : FunctorialResolution.EmbeddedResolution.preimage_basicOpen_specToAffineSpaceExtendCoords
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:21.417664+00:00
-- url     : https://prove2.me/theorems/b934b5b4-b3e2-4c6b-9f6b-d216db15dc8e
-- title:
--   Embedded Resolution: preimage basic Open spec To Affine Space Extend Coords
-- statement:
--   The Embedded Resolution construction uses the preimage basic Open spec To Affine Space Extend Coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L282-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L282-L296

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.preimage_basicOpen_specToAffineSpaceExtendCoords (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤))
    (hf : IsUnit ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f)) :
    (Opens.map (specToAffineSpaceExtendCoords k A pA M e σ n b).base).obj
        ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).basicOpen f) = ⊤ := by sorry
