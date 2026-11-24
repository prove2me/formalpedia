-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing
-- name    : FunctorialResolution.EmbeddedResolution.pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:08.263881+00:00
-- url     : https://prove2.me/theorems/742f013e-c138-4539-9f23-77a21b47f6a2
-- title:
--   Embedded Resolution: pderiv mv Polynomial Equiv Global Sections symm mv Polynomial To Sum Coordinate Ring
-- statement:
--   The Embedded Resolution construction uses the pderiv mv Polynomial Equiv Global Sections symm mv Polynomial To Sum Coordinate Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L162-L173

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SumCoordinatePartialDerivatives
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

theorem FunctorialResolution.EmbeddedResolution.pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p)) =
      (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv i p)) := by sorry
