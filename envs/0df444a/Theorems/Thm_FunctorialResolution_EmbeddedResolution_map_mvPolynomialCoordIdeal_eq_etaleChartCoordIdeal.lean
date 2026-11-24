-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal
-- name    : FunctorialResolution.EmbeddedResolution.map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:47.836745+00:00
-- url     : https://prove2.me/theorems/8ccfdca2-c521-4ff5-9a5c-a6c286ce99dd
-- title:
--   Embedded Resolution: map mv Polynomial Coord Ideal eq etale Chart Coord Ideal
-- statement:
--   The Embedded Resolution construction uses the map mv Polynomial Coord Ideal eq etale Chart Coord Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateQuotient.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateQuotient.lean#L29-L34

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    Ideal.map (algebraMap (CoordPolynomialRing k m) S) (mvPolynomialCoordIdeal k m J) =
      etaleChartCoordIdeal k m S J := by sorry
