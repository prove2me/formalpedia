-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq
-- name    : FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:31.201856+00:00
-- url     : https://prove2.me/theorems/08516bc3-f536-4aec-9ee8-7780dc7d1549
-- title:
--   Embedded Resolution: graph Morphism To Affine Space basic Open jacobian Det Section eq
-- statement:
--   The Embedded Resolution construction uses the graph Morphism To Affine Space basic Open jacobian Det Section eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChartSmooth.lean#L454-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChartSmooth.lean#L454-L582

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChart
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraSpecSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChartSmooth
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

theorem FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    graphMorphismToAffineSpace k M n q F
        ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
          (jacobianDetSection k M n q F s)) =
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv := by sorry
