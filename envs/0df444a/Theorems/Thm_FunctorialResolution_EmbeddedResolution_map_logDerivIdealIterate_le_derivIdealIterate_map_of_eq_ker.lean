-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker
-- name    : FunctorialResolution.EmbeddedResolution.map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:38.689043+00:00
-- url     : https://prove2.me/theorems/49e5b309-42fe-44e9-a591-0a0474028f95
-- title:
--   Embedded Resolution: map log Deriv Ideal Iterate le deriv Ideal Iterate map of eq ker
-- statement:
--   The Embedded Resolution construction uses the map log Deriv Ideal Iterate le deriv Ideal Iterate map of eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealQuotient.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealQuotient.lean#L40-L46

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

theorem FunctorialResolution.EmbeddedResolution.map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker (f : S →ₐ[k] T)
    (hf : Function.Surjective f) {P : Ideal S} (hP : P = RingHom.ker f.toRingHom)
    (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by sorry
