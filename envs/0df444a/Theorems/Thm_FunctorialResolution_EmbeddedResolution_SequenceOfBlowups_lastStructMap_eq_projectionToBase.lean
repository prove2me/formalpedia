-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_lastStructMap_eq_projectionToBase
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.lastStructMap_eq_projectionToBase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:39.009793+00:00
-- url     : https://prove2.me/theorems/5ac46cb2-1e3e-459b-b01f-88b491ed1983
-- title:
--   Sequence Of Blowups: last Struct Map eq projection To Base
-- statement:
--   The Sequence Of Blowups construction uses the last Struct Map eq projection To Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceBasic.lean#L39-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceBasic.lean#L39-L39

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
variable {X : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.lastStructMap_eq_projectionToBase (s : SequenceOfBlowups X) : s.lastStructMap = s.projectionToBase s.length := by sorry
