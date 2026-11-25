-- Prove2me | Theorems.Thm_GlobalTheory_exists_graded_ring_kernel_lift
-- name    : GlobalTheory.exists_graded_ring_kernel_lift
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:56.753087+00:00
-- url     : https://prove2.me/theorems/2ab16cc7-bcae-5638-a770-76a9db91232f
-- title:
--   Global Theory: exists graded ring kernel lift
-- statement:
--   The Global Theory construction uses the exists graded ring kernel lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean#L30-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean#L30-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.exists_graded_ring_kernel_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∃ (S : Type) (_ : CommRing S) (g : R →+* S), IsNoetherianRing S ∧ (∀ x ∈ I, g x = 0) ∧ ∀ (e : ℕ) (g' : R ⧸ I ^ (e + 1 + 1) →+* S), g'.comp (Ideal.Quotient.mk _) = g → ∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) (R ⧸ I ^ (e + 1 + 1))) (D₁ : Matrix (Fin c) (Fin b) (R ⧸ I ^ (e + 1 + 1))), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g').mulVec w = 0 → ∃ v, (D₀.map g').mulVec v = w) → ∀ v' : Fin a → R ⧸ I ^ (e + 1), (D₀.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1))).mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1)) (v k) = v' k := by sorry
