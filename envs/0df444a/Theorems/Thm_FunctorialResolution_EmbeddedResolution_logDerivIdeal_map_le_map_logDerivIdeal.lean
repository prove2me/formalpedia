-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_map_le_map_logDerivIdeal
-- name    : FunctorialResolution.EmbeddedResolution.logDerivIdeal_map_le_map_logDerivIdeal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:23.725337+00:00
-- url     : https://prove2.me/theorems/5b498111-aa65-4ebf-9a49-3f1870e99fa8
-- title:
--   Embedded Resolution: log Deriv Ideal map le map log Deriv Ideal
-- statement:
--   The Embedded Resolution construction uses the log Deriv Ideal map le map log Deriv Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L155-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L155-L190

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

theorem FunctorialResolution.EmbeddedResolution.logDerivIdeal_map_le_map_logDerivIdeal (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by sorry
