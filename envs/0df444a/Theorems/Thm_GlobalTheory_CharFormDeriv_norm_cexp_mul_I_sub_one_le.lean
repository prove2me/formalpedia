-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_le
-- name    : GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:20.585443+00:00
-- url     : https://prove2.me/theorems/7da0bdae-2d4c-4e09-8fca-edae97271966
-- title:
--   Char Form Deriv: norm cexp mul I sub one le
-- statement:
--   The Char Form Deriv construction uses the norm cexp mul I sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L36-L43

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

theorem GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le (z : ℝ) : ‖Complex.exp (z * I) - 1‖ ≤ 2 * |z| := by sorry
