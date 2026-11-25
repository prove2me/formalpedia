-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_dense_preimage_smoothLocus
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.dense_preimage_smoothLocus
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:52.561627+00:00
-- url     : https://prove2.me/theorems/4d91061b-73da-4231-806b-f74521c928a2
-- title:
--   Local Resolution Data: dense preimage smooth Locus
-- statement:
--   The Local Resolution Data construction uses the dense preimage smooth Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionDense.lean#L18-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionDense.lean#L18-L44

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionDense
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

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by sorry
