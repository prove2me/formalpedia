-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_deriv_affine_cexp
-- name    : GlobalTheory.CharFormDeriv.deriv_affine_cexp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:28.379174+00:00
-- url     : https://prove2.me/theorems/43f9a2a5-4159-48ae-980c-32c558fed19b
-- title:
--   Char Form Deriv: deriv affine cexp
-- statement:
--   The Char Form Deriv construction uses the deriv affine cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L25-L34

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

theorem GlobalTheory.CharFormDeriv.deriv_affine_cexp (a c d e : ℂ) :
    deriv (fun y : ℝ => c * Complex.exp (a * y) + d * y + e) =
      fun y : ℝ => c * a * Complex.exp (a * y) + d := by sorry
