-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
-- name    : FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:02.701956+00:00
-- url     : https://prove2.me/theorems/a33a8e4b-1d2b-402b-b7f5-3344e14d9c1d
-- title:
--   Embedded Resolution: coord Vector Inr inr
-- statement:
--   The Embedded Resolution construction uses the coord Vector Inr inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L53-L55

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

theorem FunctorialResolution.EmbeddedResolution.coordVectorInr_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
