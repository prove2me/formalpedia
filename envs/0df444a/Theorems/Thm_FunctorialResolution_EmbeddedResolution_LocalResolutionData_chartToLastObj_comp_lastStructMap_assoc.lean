-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_comp_lastStructMap_assoc
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.chartToLastObj_comp_lastStructMap_assoc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:46.860335+00:00
-- url     : https://prove2.me/theorems/fd512dd6-701a-4bce-89f6-1faebbb9728f
-- title:
--   Local Resolution Data: chart To Last Obj comp last Struct Map assoc
-- statement:
--   The Local Resolution Data construction uses the chart To Last Obj comp last Struct Map assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionSmooth.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionSmooth.lean#L18-L20

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

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.chartToLastObj_comp_lastStructMap_assoc (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by sorry
