-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_pderiv_inr_renameSumInl
-- name    : FunctorialResolution.EmbeddedResolution.pderiv_inr_renameSumInl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:31.183446+00:00
-- url     : https://prove2.me/theorems/e720e742-16a5-4b29-bbdc-61fe80c3f25e
-- title:
--   Embedded Resolution: pderiv inr rename Sum Inl
-- statement:
--   The Embedded Resolution construction uses the pderiv inr rename Sum Inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L40-L53

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

theorem FunctorialResolution.EmbeddedResolution.pderiv_inr_renameSumInl (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (renameSumInl k M n p) = 0 := by sorry
