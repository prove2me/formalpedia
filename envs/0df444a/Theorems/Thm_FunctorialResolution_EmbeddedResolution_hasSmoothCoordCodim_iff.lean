-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasSmoothCoordCodim_iff
-- name    : FunctorialResolution.EmbeddedResolution.hasSmoothCoordCodim_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:45.361336+00:00
-- url     : https://prove2.me/theorems/46af934f-c329-4cb4-8d6e-8dec81503332
-- title:
--   Embedded Resolution: has Smooth Coord Codim iff
-- statement:
--   The Embedded Resolution construction uses the has Smooth Coord Codim iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimension.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimension.lean#L20-L28

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.hasSmoothCoordCodim_iff {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) :
    HasSmoothCoordCodim s t c ↔
      ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
        (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
        AlgebraicGeometry.Smooth q ∧
          q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
          restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q := by sorry
