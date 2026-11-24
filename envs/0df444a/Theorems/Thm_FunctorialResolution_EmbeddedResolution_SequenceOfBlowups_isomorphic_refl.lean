-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isomorphic_refl
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.isomorphic_refl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:08.504547+00:00
-- url     : https://prove2.me/theorems/1f19edc9-9f5d-4343-a974-62bfba3bcea0
-- title:
--   Sequence Of Blowups: isomorphic refl
-- statement:
--   The Sequence Of Blowups construction uses the isomorphic refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L35-L36

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.isomorphic_refl {X : Scheme.{u}} (B : SequenceOfBlowups X) : B.Isomorphic B := by sorry
