-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_logDerivIdeal
-- name    : FunctorialResolution.EmbeddedResolution.derivation_apply_mem_logDerivIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:21.614715+00:00
-- url     : https://prove2.me/theorems/b2881b8d-6dc1-44d3-83f8-c6228f855b63
-- title:
--   Embedded Resolution: derivation apply mem log Deriv Ideal
-- statement:
--   The Embedded Resolution construction uses the derivation apply mem log Deriv Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdeal.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdeal.lean#L57-L61

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem FunctorialResolution.EmbeddedResolution.derivation_apply_mem_logDerivIdeal (P J : Ideal S) (D : Derivation k S S)
    (hD : D ∈ tangentDerivations k P) {x : S} (hx : x ∈ J) :
    D x ∈ logDerivIdeal k P J := by sorry
