-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_mem_pow_sub
-- name    : FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mem_pow_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:04.818635+00:00
-- url     : https://prove2.me/theorems/198b6e91-3567-4c2f-8c60-c7ecdc666f9c
-- title:
--   Embedded Resolution: multi Index Deriv mem pow sub
-- statement:
--   The Embedded Resolution construction uses the multi Index Deriv mem pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L121-L124

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mem_pow_sub {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R) (n : ℕ)
    {f : R} (hf : f ∈ J ^ n) (α : Fin h → ℕ) :
    multiIndexDeriv D α f ∈ J ^ (n - ∑ i, α i) := by sorry
