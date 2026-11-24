-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_derivIdeal_away
-- name    : FunctorialResolution.EmbeddedResolution.map_derivIdeal_away
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:06.214287+00:00
-- url     : https://prove2.me/theorems/82cdd8ac-39d1-4b9b-9695-c6b2fdfbbadf
-- title:
--   Embedded Resolution: map deriv Ideal away
-- statement:
--   The Embedded Resolution construction uses the map deriv Ideal away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealLocalization.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealLocalization.lean#L73-L77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} {S : Type v} {S' : Type w}

theorem FunctorialResolution.EmbeddedResolution.map_derivIdeal_away [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) := by sorry
