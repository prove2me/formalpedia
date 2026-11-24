-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivationOfSurjective_apply
-- name    : FunctorialResolution.EmbeddedResolution.derivationOfSurjective_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:32.30937+00:00
-- url     : https://prove2.me/theorems/4ede14ee-1a6d-48d3-9d38-ebedf60f2453
-- title:
--   Embedded Resolution: derivation Of Surjective apply
-- statement:
--   The Embedded Resolution construction uses the derivation Of Surjective apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivationOfSurjective.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivationOfSurjective.lean#L95-L99

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

theorem FunctorialResolution.EmbeddedResolution.derivationOfSurjective_apply (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) (s : S) :
    derivationOfSurjective f hf D hD (f s) = f (D s) := by sorry
