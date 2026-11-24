-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:27.052352+00:00
-- url     : https://prove2.me/theorems/292c9566-65b8-42f6-9c82-642ecb602e5e
-- title:
--   Sequence Of Blowups: projection To Base def
-- statement:
--   The Sequence Of Blowups construction uses the projection To Base def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceBasic.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceBasic.lean#L28-L29

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase i = s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom := by sorry
