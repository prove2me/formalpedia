-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdeal_le
-- name    : FunctorialResolution.EmbeddedResolution.map_logDerivIdeal_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:53.870009+00:00
-- url     : https://prove2.me/theorems/5cee13ef-90f3-4508-84ef-d541895fd2c8
-- title:
--   Embedded Resolution: map log Deriv Ideal le
-- statement:
--   The Embedded Resolution construction uses the map log Deriv Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L92-L108

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

theorem FunctorialResolution.EmbeddedResolution.map_logDerivIdeal_le (M : Submonoid S) [IsLocalization M S'] (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) := by sorry
