-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_nil
-- name    : FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_nil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:16.763823+00:00
-- url     : https://prove2.me/theorems/f579f7c0-25e5-4820-83eb-81e0697fbda4
-- title:
--   Embedded Resolution: in Strict Normal Crossing Position nil
-- statement:
--   The Embedded Resolution construction uses the in Strict Normal Crossing Position nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsNil.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsNil.lean#L25-L31

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsNil
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

theorem FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_nil {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] :
    InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) := by sorry
