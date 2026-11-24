-- Prove2me | Theorems.Thm_GlobalTheory_Div_CMAlgChar_algChar_eq_arg_mul_abs
-- name    : GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:50:44.392191+00:00
-- url     : https://prove2.me/theorems/f9792da3-090d-4c27-a050-c6082b420f2a
-- title:
--   CMAlg Char: alg Char eq arg mul abs
-- statement:
--   The CMAlg Char construction uses the alg Char eq arg mul abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbs.lean#L54-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbs.lean#L54-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.CMAlgChar

theorem GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by sorry
