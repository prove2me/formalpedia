-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_appTop_specToAffineSpaceExtendCoords_jacobianDetSection
-- name    : FunctorialResolution.EmbeddedResolution.appTop_specToAffineSpaceExtendCoords_jacobianDetSection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:14:09.857594+00:00
-- url     : https://prove2.me/theorems/d70bd02d-da8e-485f-9d65-a9f78d99d02a
-- title:
--   Embedded Resolution: app Top spec To Affine Space Extend Coords jacobian Det Section
-- statement:
--   The Embedded Resolution construction uses the app Top spec To Affine Space Extend Coords jacobian Det Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothPullbackGraphChart.lean#L49-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothPullbackGraphChart.lean#L49-L86

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChart
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChartSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffinePullbackPresentation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SumCoordinatePartialDerivatives
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothPullbackGraphChart
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

theorem FunctorialResolution.EmbeddedResolution.appTop_specToAffineSpaceExtendCoords_jacobianDetSection (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n q : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j)
    (s : Fin q → Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s) =
      (Scheme.ΓSpecIso B').inv
        (Matrix.det (Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ σ.hom b ((MvPolynomial.pderiv (s i)) (rel j)))) := by sorry
