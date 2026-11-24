-- Prove2me | Theorems.Thm_GlobalTheory_RestrictScalarsSpan_mul_mem_span
-- name    : GlobalTheory.RestrictScalarsSpan.mul_mem_span
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:11.002973+00:00
-- url     : https://prove2.me/theorems/c0ccf62b-aa25-4f34-9a61-4c4e9311d35b
-- title:
--   Restrict Scalars Span: mul mem span
-- statement:
--   The Restrict Scalars Span construction uses the mul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/RestrictScalarsMapEqSpan.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/RestrictScalarsMapEqSpan.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.RestrictScalarsSpan

theorem GlobalTheory.RestrictScalarsSpan.mul_mem_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4} [Field K] [Field L]
    [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) (b x : B) (hx : x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) :
    b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by sorry
