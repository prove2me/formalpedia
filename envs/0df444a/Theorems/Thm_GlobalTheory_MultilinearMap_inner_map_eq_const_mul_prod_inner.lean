-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearMap_inner_map_eq_const_mul_prod_inner
-- name    : GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:57.714778+00:00
-- url     : https://prove2.me/theorems/91c208b6-a880-4d2b-9168-10abf84cd5fa
-- title:
--   Multilinear Map: inner map eq const mul prod inner
-- statement:
--   The Multilinear Map construction uses the inner map eq const mul prod inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InnerMapEqConstMulProdInner.lean#L6-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InnerMapEqConstMulProdInner.lean#L6-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InnerMapEqConstMulProdInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner
    {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)]
    [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : MultilinearMap ℂ Xs E) (K : ℝ) (hf : ∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) :
    ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by sorry
