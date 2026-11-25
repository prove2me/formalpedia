-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_addChar_apply
-- name    : GlobalTheory.isIntegral_addChar_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:56:00.617827+00:00
-- url     : https://prove2.me/theorems/11ccc70a-8365-5af0-b9bd-d77e9dcf271c
-- title:
--   Global Theory: is Integral add Char apply
-- statement:
--   The Global Theory construction uses the is Integral add Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexMatrixGaussSumNormIntegralGalois.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexMatrixGaussSumNormIntegralGalois.lean#L25-L28

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

theorem GlobalTheory.isIntegral_addChar_apply {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (x : k) :
    IsIntegral ℤ (ψ x) := by sorry
