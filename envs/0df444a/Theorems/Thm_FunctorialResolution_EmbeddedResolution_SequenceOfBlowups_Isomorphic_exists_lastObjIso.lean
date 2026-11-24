-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_exists_lastObjIso
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.Isomorphic.exists_lastObjIso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:34.835307+00:00
-- url     : https://prove2.me/theorems/0ee1f226-5c3a-4a12-8d0c-940780517dda
-- title:
--   Isomorphic: exists last Obj Iso
-- statement:
--   The Isomorphic construction uses the exists last Obj Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/SequenceIsomorphism.lean#L255-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/SequenceIsomorphism.lean#L255-L262

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.Isomorphic.exists_lastObjIso {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') :
    ∃ e : B.lastObj ≅ B'.lastObj, e.hom ≫ B'.lastStructMap = B.lastStructMap := by sorry
