-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SmoothLocalChart_isPullback_morphismRestrict_basicOpen
-- name    : FunctorialResolution.EmbeddedResolution.SmoothLocalChart.isPullback_morphismRestrict_basicOpen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:42.888774+00:00
-- url     : https://prove2.me/theorems/666b2691-503c-5799-b2fa-f68a57cd51b4
-- title:
--   Smooth Local Chart: is Pullback morphism Restrict basic Open
-- statement:
--   The Smooth Local Chart construction uses the is Pullback morphism Restrict basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothLocalChart.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothLocalChart.lean#L68-L72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothLocalChart
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
open FunctorialResolution.EmbeddedResolution.SmoothLocalChart
variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}

theorem FunctorialResolution.EmbeddedResolution.SmoothLocalChart.isPullback_morphismRestrict_basicOpen (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb := by sorry
