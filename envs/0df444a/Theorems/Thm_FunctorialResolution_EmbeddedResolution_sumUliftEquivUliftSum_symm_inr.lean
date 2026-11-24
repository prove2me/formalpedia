-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inr
-- name    : FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:24.350173+00:00
-- url     : https://prove2.me/theorems/d60fdfe6-f5c4-4697-a1dc-c2e37fc8ce04
-- title:
--   Embedded Resolution: sum Ulift Equiv Ulift Sum symm inr
-- statement:
--   The Embedded Resolution construction uses the sum Ulift Equiv Ulift Sum symm inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L146-L147

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

theorem FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inr (n m : ℕ) (b : Fin m) :
    (sumUliftEquivUliftSum.{u} n m).symm (ULift.up (Sum.inr b)) = Sum.inr (ULift.up b) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inr
