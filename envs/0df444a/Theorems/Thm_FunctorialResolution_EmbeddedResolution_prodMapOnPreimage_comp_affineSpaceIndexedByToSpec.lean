-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_prodMapOnPreimage_comp_affineSpaceIndexedByToSpec
-- name    : FunctorialResolution.EmbeddedResolution.prodMapOnPreimage_comp_affineSpaceIndexedByToSpec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:07:34.759797+00:00
-- url     : https://prove2.me/theorems/6671ebfd-b7bd-4723-b882-f821b35c61b9
-- title:
--   Embedded Resolution: prod Map On Preimage comp affine Space Indexed By To Spec
-- statement:
--   The Embedded Resolution construction uses the prod Map On Preimage comp affine Space Indexed By To Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean#L224-L229

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

theorem FunctorialResolution.EmbeddedResolution.prodMapOnPreimage_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    prodMapOnPreimage k n m c U φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c ⊕ Fin m)) =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by sorry
