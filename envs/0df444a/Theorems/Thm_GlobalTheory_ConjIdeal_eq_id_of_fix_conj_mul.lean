-- Prove2me | Theorems.Thm_GlobalTheory_ConjIdeal_eq_id_of_fix_conj_mul
-- name    : GlobalTheory.ConjIdeal.eq_id_of_fix_conj_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:20.733191+00:00
-- url     : https://prove2.me/theorems/00bd44d7-c5ed-441d-855c-adb372c380b4
-- title:
--   Conj Ideal: eq id of fix conj mul
-- statement:
--   The Conj Ideal construction uses the eq id of fix conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L188-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L188-L202

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

theorem GlobalTheory.ConjIdeal.eq_id_of_fix_conj_mul (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [CommGroup N] [CommGroup A]
    (hN : ∀ x : N, x ^ M = 1) (act : O → N →* N) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : N → N → A) (e_mul : ∀ x x' y, e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 1) → x = 1)
    (e_adj : ∀ a x y, e (act a x) y = e x (act (bar a) y))
    (θ : N →* N) (θ_act : ∀ a x, θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (act a y) = act a y) : θ = MonoidHom.id N := by sorry
