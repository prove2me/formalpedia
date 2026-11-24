-- Prove2me | Theorems.Thm_GlobalTheory_T_cm_algChar_eq_arg_mul_abs
-- name    : GlobalTheory.T.cm_algChar_eq_arg_mul_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:40.215736+00:00
-- url     : https://prove2.me/theorems/f7da1b1f-96be-4fd3-9879-42854eb0a235
-- title:
--   T: cm alg Char eq arg mul abs
-- statement:
--   The T construction uses the cm alg Char eq arg mul abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbsStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbsStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cm_algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by sorry
