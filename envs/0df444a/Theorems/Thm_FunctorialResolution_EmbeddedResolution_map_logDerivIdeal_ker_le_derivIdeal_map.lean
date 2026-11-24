-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdeal_ker_le_derivIdeal_map
-- name    : FunctorialResolution.EmbeddedResolution.map_logDerivIdeal_ker_le_derivIdeal_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:38.432895+00:00
-- url     : https://prove2.me/theorems/5aa978ac-dd28-4529-8caa-75a020f29850
-- title:
--   Embedded Resolution: map log Deriv Ideal ker le deriv Ideal map
-- statement:
--   The Embedded Resolution construction uses the map log Deriv Ideal ker le deriv Ideal map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealQuotient.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealQuotient.lean#L11-L28

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

theorem FunctorialResolution.EmbeddedResolution.map_logDerivIdeal_ker_le_derivIdeal_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by sorry
