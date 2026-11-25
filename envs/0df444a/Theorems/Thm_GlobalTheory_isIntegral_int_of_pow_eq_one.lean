-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_int_of_pow_eq_one
-- name    : GlobalTheory.isIntegral_int_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:51:29.826794+00:00
-- url     : https://prove2.me/theorems/2c5c56bc-14a4-5f83-85db-42d9783e12d3
-- title:
--   Global Theory: is Integral int of pow eq one
-- statement:
--   The Global Theory construction uses the is Integral int of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexMatrixGaussSumNormIntegralGalois.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexMatrixGaussSumNormIntegralGalois.lean#L16-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComplexMatrixGaussSumNormIntegralGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory

theorem GlobalTheory.isIntegral_int_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z := by sorry
