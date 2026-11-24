-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_away_map_ideal_eq
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_map_ideal_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:09.832027+00:00
-- url     : https://prove2.me/theorems/d0e7b93e-3d78-4da8-8b49-53add6148bf4
-- title:
--   Etale Coordinates: exists away map ideal eq
-- statement:
--   The Etale Coordinates construction uses the exists away map ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealGeneratorsFromBase.lean#L22-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealGeneratorsFromBase.lean#L22-L82

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealGeneratorsFromBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_map_ideal_eq {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
    (I J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (h : Ideal.map (algebraMap S A) I = Ideal.map (algebraMap S A) J) :
    ∃ g : S, g ∉ q ∧
      Ideal.map (algebraMap S (Localization.Away g)) I =
        Ideal.map (algebraMap S (Localization.Away g)) J := by sorry
