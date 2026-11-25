-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphMorphismToAffineSpace_eq_homOfVector
-- name    : FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_eq_homOfVector
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:04.027566+00:00
-- url     : https://prove2.me/theorems/0bc354ef-b026-490a-ae07-d0867e17f925
-- title:
--   Embedded Resolution: graph Morphism To Affine Space eq hom Of Vector
-- statement:
--   The Embedded Resolution construction uses the graph Morphism To Affine Space eq hom Of Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChart.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChart.lean#L30-L45

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

theorem FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_eq_homOfVector (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    graphMorphismToAffineSpace k M n q F D =
      AffineSpace.homOfVector
        (D.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
        (fun i =>
          Sum.elim
            (fun a : Fin M =>
              (ConcreteCategory.hom (Scheme.Hom.appTop D.ι))
                (AffineSpace.coord (Spec (CommRingCat.of k))
                  (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n))))
            (fun j : Fin q => (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j))
            i.down) := by sorry
