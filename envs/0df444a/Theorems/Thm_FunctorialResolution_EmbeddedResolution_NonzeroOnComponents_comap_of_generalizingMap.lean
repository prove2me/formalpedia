-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_NonzeroOnComponents_comap_of_generalizingMap
-- name    : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents.comap_of_generalizingMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:37.022585+00:00
-- url     : https://prove2.me/theorems/fbf09eb0-54b2-469f-bc72-a2699648f89d
-- title:
--   Nonzero On Components: comap of generalizing Map
-- statement:
--   The Nonzero On Components construction uses the comap of generalizing Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SupportFlatPullback.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SupportFlatPullback.lean#L75-L86

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

theorem FunctorialResolution.EmbeddedResolution.NonzeroOnComponents.comap_of_generalizingMap {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y)
    (hf : GeneralizingMap (fun x : ↥X => f x)) :
    NonzeroOnComponents (I.comap f) := by sorry
