-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_projLeft_appTop
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_projLeft_appTop
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:32.031636+00:00
-- url     : https://prove2.me/theorems/91f34f4f-bd4d-4083-90a9-bae663335ce7
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections symm proj Left app Top
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections symm proj Left app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L77-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L77-L101

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_projLeft_appTop (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        ((projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) p)) =
      renameSumInl k M n p := by sorry
