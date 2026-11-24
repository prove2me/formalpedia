-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_localization_atPrime_etale
-- name    : FunctorialResolution.EmbeddedResolution.isRegularLocalRing_localization_atPrime_etale
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:48:23.463798+00:00
-- url     : https://prove2.me/theorems/b2545cf2-5c5e-4477-a32b-179e3a390607
-- title:
--   Embedded Resolution: is Regular Local Ring localization at Prime etale
-- statement:
--   The Embedded Resolution construction uses the is Regular Local Ring localization at Prime etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinatePolynomialRing.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinatePolynomialRing.lean#L108-L112

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
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

theorem FunctorialResolution.EmbeddedResolution.isRegularLocalRing_localization_atPrime_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by sorry
