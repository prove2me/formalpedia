-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphMorphismToAffineSpace_appTop_coord_inr
-- name    : FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_appTop_coord_inr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:25.856812+00:00
-- url     : https://prove2.me/theorems/c897e1ec-45ae-459a-b9b2-e9e3e3438c30
-- title:
--   Embedded Resolution: graph Morphism To Affine Space app Top coord inr
-- statement:
--   The Embedded Resolution construction uses the graph Morphism To Affine Space app Top coord inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChart.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChart.lean#L67-L75

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChart
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

theorem FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_appTop_coord_inr (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) (j : Fin q) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D)))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u, 0} (Fin M ⊕ Fin q))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j) := by sorry
