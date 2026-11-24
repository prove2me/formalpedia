-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_X
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:10.946359+00:00
-- url     : https://prove2.me/theorems/d40eea3c-9a7e-4e0b-ace1-de835a1db308
-- title:
--   Embedded Resolution: mv Polynomial To Sum Coordinate Ring X
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial To Sum Coordinate Ring X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PolynomialRingOverGlobalSections.lean#L33-L37

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_X (k : Type u) [Field k] (M n : ℕ) (i : Fin n) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) := by sorry
