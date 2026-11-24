-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
-- name    : FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:52.60569+00:00
-- url     : https://prove2.me/theorems/af48803c-bf10-4d0d-aa00-d9ffb6a14076
-- title:
--   Embedded Resolution: coord Vector Inl inl
-- statement:
--   The Embedded Resolution construction uses the coord Vector Inl inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L33-L35

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

theorem FunctorialResolution.EmbeddedResolution.coordVectorInl_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (a : Fin n) :
    coordVectorInl n m f (ULift.up (Sum.inl a)) = pullbackCoord f (ULift.up a) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
