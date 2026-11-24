-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_invariantForm_translate_eq_zero
-- name    : GlobalTheory.FinWeil.invariantForm_translate_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:07.69608+00:00
-- url     : https://prove2.me/theorems/e08d528a-4516-4568-988c-0d46abf0464b
-- title:
--   Fin Weil: invariant Form translate eq zero
-- statement:
--   The Fin Weil construction uses the invariant Form translate eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantFormNormalizedHeisenbergIntertwinerEq.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantFormNormalizedHeisenbergIntertwinerEq.lean#L14-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem GlobalTheory.FinWeil.invariantForm_translate_eq_zero (h : IsHeis σ w γ W) {P Q : X →ₗ[R] X} (hPP : ∀ x, P (P x) = P x)
    (hadj : ∀ x y, γ (P x) y = γ x (Q y)) {C : Submodule R X} (hC : SelfDual γ C) (hQC : ∀ a ∈ C, Q a ∈ C)
    (ℓ : M →ₗ[ℂ] ℂ) (hl : ∀ u m, ℓ (W (Q u) m) = ℓ m) {e : M} (he : Fixes W C e) {z : X} (hz : P z ∉ C) :
    ℓ (W (P z) e) = 0 := by sorry
