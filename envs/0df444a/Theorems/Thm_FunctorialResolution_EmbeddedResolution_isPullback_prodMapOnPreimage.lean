-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_prodMapOnPreimage
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_prodMapOnPreimage
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:31.343694+00:00
-- url     : https://prove2.me/theorems/9d43c9ef-a5e7-4324-aa67-e1d66f487a55
-- title:
--   Embedded Resolution: is Pullback prod Map On Preimage
-- statement:
--   The Embedded Resolution construction uses the is Pullback prod Map On Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L269-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L269-L288

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

theorem FunctorialResolution.EmbeddedResolution.isPullback_prodMapOnPreimage (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    IsPullback (prodMapOnPreimage k n m c U φ)
      (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k c m) φ := by sorry
