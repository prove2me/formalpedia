-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_isIso_lastStructMap_restrict_smoothLocus
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.isIso_lastStructMap_restrict_smoothLocus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:29.185173+00:00
-- url     : https://prove2.me/theorems/a47a92ed-e4e1-5be4-a037-b69dbd646aa3
-- title:
--   Local Resolution Data: is Iso last Struct Map restrict smooth Locus
-- statement:
--   The Local Resolution Data construction uses the is Iso last Struct Map restrict smooth Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/SmoothLocusIsomorphism.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/SmoothLocusIsomorphism.lean#L84-L92

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

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.isIso_lastStructMap_restrict_smoothLocus (d : LocalResolutionData k f s) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by sorry
