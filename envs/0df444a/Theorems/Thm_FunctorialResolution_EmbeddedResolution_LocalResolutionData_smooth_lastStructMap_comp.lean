-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_smooth_lastStructMap_comp
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.smooth_lastStructMap_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:54.10303+00:00
-- url     : https://prove2.me/theorems/4180abb8-a250-56e6-9797-6a1e5262c889
-- title:
--   Local Resolution Data: smooth last Struct Map comp
-- statement:
--   The Local Resolution Data construction uses the smooth last Struct Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionSmooth.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionSmooth.lean#L50-L60

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionSmooth
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
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.smooth_lastStructMap_comp (d : LocalResolutionData k f s) :
    AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) := by sorry
