-- Prove2me | Theorems.Thm_GlobalTheory_ConjIdeal_eq_id_of_fix_conj
-- name    : GlobalTheory.ConjIdeal.eq_id_of_fix_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:28.163452+00:00
-- url     : https://prove2.me/theorems/d3785b88-34f7-487e-8c4b-93a3f0019500
-- title:
--   Conj Ideal: eq id of fix conj
-- statement:
--   The Conj Ideal construction uses the eq id of fix conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L204-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L204-L222

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

theorem GlobalTheory.ConjIdeal.eq_id_of_fix_conj (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [AddCommGroup N] [Module O N]
    [AddCommGroup A] (hN : ∀ x : N, M • x = 0)
    (e : N → N → A) (e_add : ∀ x x' y, e (x + x') y = e x y + e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 0) → x = 0)
    (e_adj : ∀ (a : O) x y, e (a • x) y = e x (bar a • y))
    (θ : N →ₗ[O] N) (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) : θ = LinearMap.id := by sorry
