-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_map_span_singleton_prod_etaleChartCoord
-- name    : FunctorialResolution.EmbeddedResolution.isRadical_map_span_singleton_prod_etaleChartCoord
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:30.716279+00:00
-- url     : https://prove2.me/theorems/0496f6e8-ac85-4aeb-9a31-e1d11d1e9bf8
-- title:
--   Embedded Resolution: is Radical map span singleton prod etale Chart Coord
-- statement:
--   The Embedded Resolution construction uses the is Radical map span singleton prod etale Chart Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorRadical.lean#L216-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorRadical.lean#L216-L244

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
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

theorem FunctorialResolution.EmbeddedResolution.isRadical_map_span_singleton_prod_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (T : Finset (Fin m)) :
    (Ideal.map (algebraMap S A)
      (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S))).IsRadical := by sorry
