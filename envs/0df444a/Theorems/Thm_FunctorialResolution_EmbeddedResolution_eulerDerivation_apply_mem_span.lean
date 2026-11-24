-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_eulerDerivation_apply_mem_span
-- name    : FunctorialResolution.EmbeddedResolution.eulerDerivation_apply_mem_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:49.675134+00:00
-- url     : https://prove2.me/theorems/1d9527a0-4af7-4388-8a95-4018aceb1f9d
-- title:
--   Embedded Resolution: euler Derivation apply mem span
-- statement:
--   The Embedded Resolution construction uses the euler Derivation apply mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealOrderDecrease.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealOrderDecrease.lean#L28-L32

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing

theorem FunctorialResolution.EmbeddedResolution.eulerDerivation_apply_mem_span (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a ∈ Ideal.span (Set.range x) := by sorry
