-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:21.612985+00:00
-- url     : https://prove2.me/theorems/52f69515-34ac-4982-91d3-a5f13b8c8548
-- title:
--   Sequence Of Blowups: is Blowup Along Ideal Sheaf blowup Morphism
-- statement:
--   The Sequence Of Blowups construction uses the is Blowup Along Ideal Sheaf blowup Morphism property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceBasic.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceBasic.lean#L25-L26

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) (h : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := by sorry
