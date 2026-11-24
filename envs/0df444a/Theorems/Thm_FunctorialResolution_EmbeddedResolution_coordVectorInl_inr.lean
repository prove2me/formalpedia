-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
-- name    : FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:07.314654+00:00
-- url     : https://prove2.me/theorems/1a80b4ed-16f9-4473-bc2c-ab964529ae29
-- title:
--   Embedded Resolution: coord Vector Inl inr
-- statement:
--   The Embedded Resolution construction uses the coord Vector Inl inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L38-L40

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
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

theorem FunctorialResolution.EmbeddedResolution.coordVectorInl_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (b : Fin m) :
    coordVectorInl n m f (ULift.up (Sum.inr b)) = 0 := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
