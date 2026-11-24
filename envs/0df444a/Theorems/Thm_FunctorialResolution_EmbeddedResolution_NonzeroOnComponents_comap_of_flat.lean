-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_NonzeroOnComponents_comap_of_flat
-- name    : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents.comap_of_flat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:52.476075+00:00
-- url     : https://prove2.me/theorems/3f51c290-ef29-4539-8025-db9a84a59258
-- title:
--   Nonzero On Components: comap of flat
-- statement:
--   The Nonzero On Components construction uses the comap of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SupportFlatPullback.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SupportFlatPullback.lean#L88-L91

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
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
open FunctorialResolution.EmbeddedResolution.NonzeroOnComponents

theorem FunctorialResolution.EmbeddedResolution.NonzeroOnComponents.comap_of_flat {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    NonzeroOnComponents (I.comap f) := by sorry
