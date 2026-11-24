-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoordIdeal_eq_span_image
-- name    : FunctorialResolution.EmbeddedResolution.etaleChartCoordIdeal_eq_span_image
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:34.60314+00:00
-- url     : https://prove2.me/theorems/c053653e-cbba-4aa5-9bf4-74da92392a7a
-- title:
--   Embedded Resolution: etale Chart Coord Ideal eq span image
-- statement:
--   The Embedded Resolution construction uses the etale Chart Coord Ideal eq span image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateQuotient.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateQuotient.lean#L17-L20

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

theorem FunctorialResolution.EmbeddedResolution.etaleChartCoordIdeal_eq_span_image (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    etaleChartCoordIdeal k m S J = Ideal.span (etaleChartCoord k m S '' (J : Set (Fin m))) := by sorry
