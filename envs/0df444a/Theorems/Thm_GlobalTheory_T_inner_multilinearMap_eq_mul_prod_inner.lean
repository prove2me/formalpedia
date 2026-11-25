-- Prove2me | Theorems.Thm_GlobalTheory_T_inner_multilinearMap_eq_mul_prod_inner
-- name    : GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:57.424194+00:00
-- url     : https://prove2.me/theorems/fed4b9a8-9189-45a5-8d81-9d8bf6927b82
-- title:
--   T: inner multilinear Map eq mul prod inner
-- statement:
--   The T construction uses the inner multilinear Map eq mul prod inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InnerMapEqConstMulProdInnerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InnerMapEqConstMulProdInnerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InnerMapEqConstMulProdInner
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InnerMapEqConstMulProdInnerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner : ∀ {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)] [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : MultilinearMap ℂ Xs E) (K : ℝ), (∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) → ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by sorry
