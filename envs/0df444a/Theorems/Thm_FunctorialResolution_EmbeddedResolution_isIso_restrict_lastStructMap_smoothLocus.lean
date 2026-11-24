-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIso_restrict_lastStructMap_smoothLocus
-- name    : FunctorialResolution.EmbeddedResolution.isIso_restrict_lastStructMap_smoothLocus
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:19.315336+00:00
-- url     : https://prove2.me/theorems/ddc5990a-2c76-49ca-84f7-40d7383bb110
-- title:
--   Embedded Resolution: is Iso restrict last Struct Map smooth Locus
-- statement:
--   The Embedded Resolution construction uses the is Iso restrict last Struct Map smooth Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/IsoAwayFromCenters.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/IsoAwayFromCenters.lean#L68-L74

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_IsoAwayFromCenters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isIso_restrict_lastStructMap_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (s : SequenceOfBlowups X)
    (hs : s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by sorry
