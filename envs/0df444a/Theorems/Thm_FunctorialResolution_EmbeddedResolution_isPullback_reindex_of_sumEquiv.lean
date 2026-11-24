-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_reindex_of_sumEquiv
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_reindex_of_sumEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:46.568093+00:00
-- url     : https://prove2.me/theorems/4d03704c-bb2a-4c0a-be22-b263b66b9c4e
-- title:
--   Embedded Resolution: is Pullback reindex of sum Equiv
-- statement:
--   The Embedded Resolution construction uses the is Pullback reindex of sum Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L76-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L76-L123

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

theorem FunctorialResolution.EmbeddedResolution.isPullback_reindex_of_sumEquiv {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) :
    IsPullback
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := by sorry
