-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_specToAffineSpaceExtendCoords_appTop
-- name    : FunctorialResolution.EmbeddedResolution.ker_specToAffineSpaceExtendCoords_appTop
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:48.432833+00:00
-- url     : https://prove2.me/theorems/c8d0c064-19eb-4efc-b38d-6bf053f4be32
-- title:
--   Embedded Resolution: ker spec To Affine Space Extend Coords app Top
-- statement:
--   The Embedded Resolution construction uses the ker spec To Affine Space Extend Coords app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L190-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L190-L280

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

theorem FunctorialResolution.EmbeddedResolution.ker_specToAffineSpaceExtendCoords_appTop (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (q : ℕ) (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (hrel : RingHom.ker (MvPolynomial.eval₂Hom σ.hom b) = Ideal.span (Set.range rel))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j) :
    RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom =
      Ideal.map ((projLeft k M n).appTop).hom (RingHom.ker (e.appTop).hom)
        ⊔ Ideal.span (Set.range fun j : Fin q => mvPolynomialToSumCoordinateRing k M n (lift j)) := by sorry
