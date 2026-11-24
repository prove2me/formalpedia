-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inl
-- name    : FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:46.277806+00:00
-- url     : https://prove2.me/theorems/81ff3c08-7b81-4759-ac03-81353af05b90
-- title:
--   Embedded Resolution: sum Ulift Equiv Ulift Sum symm inl
-- statement:
--   The Embedded Resolution construction uses the sum Ulift Equiv Ulift Sum symm inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L142-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L142-L143

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
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

theorem FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inl (n m : ℕ) (a : Fin n) :
    (sumUliftEquivUliftSum.{u} n m).symm (ULift.up (Sum.inl a)) = Sum.inl (ULift.up a) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inl
