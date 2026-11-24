-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_mvPolynomial_map_appTop_eq
-- name    : FunctorialResolution.EmbeddedResolution.exists_mvPolynomial_map_appTop_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:21.774332+00:00
-- url     : https://prove2.me/theorems/466481d9-d14b-4183-b445-b00b9c10b71a
-- title:
--   Embedded Resolution: exists mv Polynomial map app Top eq
-- statement:
--   The Embedded Resolution construction uses the exists mv Polynomial map app Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L180-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L180-L188

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

theorem FunctorialResolution.EmbeddedResolution.exists_mvPolynomial_map_appTop_eq (k : Type u) [Field k] (A : Scheme.{u}) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] (n q : ℕ)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤)) (j : Fin q) :
    ∃ P : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤),
      MvPolynomial.map (e.appTop).hom P = rel j := by sorry
