-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_iteratedDeriv_const_mul_cexp
-- name    : GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:20.69795+00:00
-- url     : https://prove2.me/theorems/d797ee72-a485-4fcd-a1d8-c83c8a43f6c1
-- title:
--   Char Form Deriv: iterated Deriv const mul cexp
-- statement:
--   The Char Form Deriv construction uses the iterated Deriv const mul cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp (a c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => c * Complex.exp (a * y)) =
      fun y : ℝ => c * a ^ n * Complex.exp (a * y) := by sorry
