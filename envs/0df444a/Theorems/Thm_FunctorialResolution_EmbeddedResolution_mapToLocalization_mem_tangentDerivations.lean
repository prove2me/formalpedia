-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mapToLocalization_mem_tangentDerivations
-- name    : FunctorialResolution.EmbeddedResolution.mapToLocalization_mem_tangentDerivations
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:25.8489+00:00
-- url     : https://prove2.me/theorems/23cf26e1-92d8-4f0a-a961-06d987cba572
-- title:
--   Embedded Resolution: map To Localization mem tangent Derivations
-- statement:
--   The Embedded Resolution construction uses the map To Localization mem tangent Derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L81-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L81-L90

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

theorem FunctorialResolution.EmbeddedResolution.mapToLocalization_mem_tangentDerivations (M : Submonoid S) [IsLocalization M S']
    {P : Ideal S} {D : Derivation k S S} (hD : D ∈ tangentDerivations k P) :
    (D.mapToLocalization (S' := S') M) ∈
      tangentDerivations k (P.map (algebraMap S S')) := by sorry
