-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projLeft_projRight
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_projLeft_projRight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:24.409195+00:00
-- url     : https://prove2.me/theorems/9cc18cda-309b-413b-aa6f-fffd48f5ee81
-- title:
--   Embedded Resolution: is Pullback proj Left proj Right
-- statement:
--   The Embedded Resolution construction uses the is Pullback proj Left proj Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L187-L191

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

theorem FunctorialResolution.EmbeddedResolution.isPullback_projLeft_projRight (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := by sorry
