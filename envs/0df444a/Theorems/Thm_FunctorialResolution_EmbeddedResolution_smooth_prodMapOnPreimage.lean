-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_smooth_prodMapOnPreimage
-- name    : FunctorialResolution.EmbeddedResolution.smooth_prodMapOnPreimage
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:54.250557+00:00
-- url     : https://prove2.me/theorems/f6be9b96-bd01-4395-a7bb-15ae44b76512
-- title:
--   Embedded Resolution: smooth prod Map On Preimage
-- statement:
--   The Embedded Resolution construction uses the smooth prod Map On Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L290-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L290-L299

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

theorem FunctorialResolution.EmbeddedResolution.smooth_prodMapOnPreimage (_hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    [AlgebraicGeometry.Smooth φ]
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    AlgebraicGeometry.Smooth (prodMapOnPreimage k n m c U φ) := by sorry
