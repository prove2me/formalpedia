-- Prove2me | Theorems.Thm_GlobalTheory_natCard_eq_coker_mul_ker_of_exact
-- name    : GlobalTheory.natCard_eq_coker_mul_ker_of_exact
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:12:05.757946+00:00
-- url     : https://prove2.me/theorems/8db94c47-5bcf-41f1-be12-e783a54d188f
-- title:
--   Global Theory: nat Card eq coker mul ker of exact
-- statement:
--   The Global Theory construction uses the nat Card eq coker mul ker of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyOfShortExactMul.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyOfShortExactMul.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.natCard_eq_coker_mul_ker_of_exact {R : Type} [Ring R] {A A' B D D' : Type}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    [Module R A] [Module R A'] [Module R B] [Module R D] [Module R D']
    (f : A →ₗ[R] A') (g : A' →ₗ[R] B) (d : B →ₗ[R] D) (h : D →ₗ[R] D')
    (e₁ : LinearMap.range f = LinearMap.ker g) (e₂ : LinearMap.range g = LinearMap.ker d)
    (e₃ : LinearMap.range d = LinearMap.ker h) :
    Nat.card B = Nat.card (A' ⧸ LinearMap.range f) * Nat.card (LinearMap.ker h) := by sorry
