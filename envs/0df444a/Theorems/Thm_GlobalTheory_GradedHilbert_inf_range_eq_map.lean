-- Prove2me | Theorems.Thm_GlobalTheory_GradedHilbert_inf_range_eq_map
-- name    : GlobalTheory.GradedHilbert.inf_range_eq_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:59:01.401194+00:00
-- url     : https://prove2.me/theorems/ebcd7370-b4b1-4a31-9f95-6dfb069077d3
-- title:
--   Graded Hilbert: inf range eq map
-- statement:
--   The Graded Hilbert construction uses the inf range eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L193-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L193-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open GlobalTheory.GradedHilbert
open DirectSum
variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem GlobalTheory.GradedHilbert.inf_range_eq_map (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (𝒩 : ℤ → Submodule R N)
    [Decomposition 𝒩] (f : M →ₗ[R] N) (d : ℤ) (hf : ∀ n, ∀ m ∈ ℳ n, f m ∈ 𝒩 (n + d))
    (n : ℤ) : 𝒩 (n + d) ⊓ LinearMap.range f = (ℳ n).map f := by sorry
