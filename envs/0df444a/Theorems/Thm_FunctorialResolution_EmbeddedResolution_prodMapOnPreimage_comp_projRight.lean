-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_prodMapOnPreimage_comp_projRight
-- name    : FunctorialResolution.EmbeddedResolution.prodMapOnPreimage_comp_projRight
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:32.211996+00:00
-- url     : https://prove2.me/theorems/140add65-d2e7-43f9-9c45-c790ee708d5d
-- title:
--   Embedded Resolution: prod Map On Preimage comp proj Right
-- statement:
--   The Embedded Resolution construction uses the prod Map On Preimage comp proj Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L231-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L231-L241

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

theorem FunctorialResolution.EmbeddedResolution.prodMapOnPreimage_comp_projRight (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    prodMapOnPreimage k n m c U φ ≫ projRight k c m =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ projRight k n m := by sorry
