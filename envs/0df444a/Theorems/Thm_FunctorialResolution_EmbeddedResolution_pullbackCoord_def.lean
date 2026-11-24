-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- name    : FunctorialResolution.EmbeddedResolution.pullbackCoord_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:21.663449+00:00
-- url     : https://prove2.me/theorems/46a4d119-acc2-4c6c-a458-1d21c8855a19
-- title:
--   Embedded Resolution: pullback Coord def
-- statement:
--   The Embedded Resolution construction uses the pullback Coord def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean#L23-L25

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

theorem FunctorialResolution.EmbeddedResolution.pullbackCoord_def {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.pullbackCoord_def
