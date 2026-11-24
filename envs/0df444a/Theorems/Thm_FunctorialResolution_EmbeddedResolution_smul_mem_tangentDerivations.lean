-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_smul_mem_tangentDerivations
-- name    : FunctorialResolution.EmbeddedResolution.smul_mem_tangentDerivations
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:49.713473+00:00
-- url     : https://prove2.me/theorems/c3e2d862-89ca-461c-aa2a-354d0bc61e4b
-- title:
--   Embedded Resolution: smul mem tangent Derivations
-- statement:
--   The Embedded Resolution construction uses the smul mem tangent Derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdeal.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdeal.lean#L25-L30

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

theorem FunctorialResolution.EmbeddedResolution.smul_mem_tangentDerivations (P : Ideal S) {p : S} (hp : p ∈ P)
    (D : Derivation k S S) : p • D ∈ tangentDerivations k P := by sorry
