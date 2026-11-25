-- Prove2me | Theorems.Thm_GlobalTheory_ConjIdeal_level_rigidity
-- name    : GlobalTheory.ConjIdeal.level_rigidity
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:29.018414+00:00
-- url     : https://prove2.me/theorems/628cfbb5-132f-5121-ba8b-485194fdfcb8
-- title:
--   Conj Ideal: level rigidity
-- statement:
--   The Conj Ideal construction uses the level rigidity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L224-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L224-L238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
variable {O : Type*} [CommRing O]

theorem GlobalTheory.ConjIdeal.level_rigidity (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) (hIJ : I * I.map bar = Ideal.span {(M : O)}) :
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] (d : X →ₗ[O] X),
      (∀ x ∈ I.map bar, ∀ y, ∃ z : X, d (x • y) = M • z) →
      (∀ t : X →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) →
      ∀ y, ∃ z : X, d y = M • z) ∧
    (∀ (N A : Type) [AddCommGroup N] [Module O N] [AddCommGroup A], (∀ x : N, M • x = 0) →
      ∀ e : N →+ N →+ A, (∀ x, e x = 0 → x = 0) → (∀ (a : O) x y, e (a • x) y = e x (bar a • y)) →
      ∀ θ : N ≃ₗ[O] N, (∀ x y, e (θ x) (θ y) = e x y) → (∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) →
      θ = LinearEquiv.refl O N) := by sorry
