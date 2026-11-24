-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_renameSumInl_X
-- name    : FunctorialResolution.EmbeddedResolution.renameSumInl_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:12.407108+00:00
-- url     : https://prove2.me/theorems/4206161e-58c7-48f4-a30f-11734424daf8
-- title:
--   Embedded Resolution: rename Sum Inl X
-- statement:
--   The Embedded Resolution construction uses the rename Sum Inl X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SumCoordinatePartialDerivatives.lean#L28-L31

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

theorem FunctorialResolution.EmbeddedResolution.renameSumInl_X (k : Type u) [Field k] (M n : ℕ) (a : Fin M) :
    renameSumInl k M n (MvPolynomial.X (ULift.up a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) := by sorry
