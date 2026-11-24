-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPositionAt_nil
-- name    : FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_nil
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:19.017545+00:00
-- url     : https://prove2.me/theorems/99bf27fe-bc43-4294-9823-c539588348c4
-- title:
--   Embedded Resolution: in Strict Normal Crossing Position At nil
-- statement:
--   The Embedded Resolution construction uses the in Strict Normal Crossing Position At nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsNil.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsNil.lean#L12-L23

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

theorem FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_nil {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    InStrictNormalCrossingPositionAt p ([] : List X.IdealSheafData) x := by sorry
