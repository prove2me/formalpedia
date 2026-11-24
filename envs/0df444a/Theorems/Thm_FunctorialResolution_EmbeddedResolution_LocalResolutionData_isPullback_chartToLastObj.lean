-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_isPullback_chartToLastObj
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.isPullback_chartToLastObj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:53.40998+00:00
-- url     : https://prove2.me/theorems/3e455c41-620d-4087-bd15-9deb899d7bac
-- title:
--   Local Resolution Data: is Pullback chart To Last Obj
-- statement:
--   The Local Resolution Data construction uses the is Pullback chart To Last Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/SmoothLocusIsomorphism.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/SmoothLocusIsomorphism.lean#L18-L25

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SmoothLocusIsomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.isPullback_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap (d.cover.f i) := by sorry
