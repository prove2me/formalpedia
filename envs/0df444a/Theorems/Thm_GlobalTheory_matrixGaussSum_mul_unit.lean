-- Prove2me | Theorems.Thm_GlobalTheory_matrixGaussSum_mul_unit
-- name    : GlobalTheory.matrixGaussSum_mul_unit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:13.650305+00:00
-- url     : https://prove2.me/theorems/20af9767-8a52-4c59-9870-5667b796cad9
-- title:
--   Global Theory: matrix Gauss Sum mul unit
-- statement:
--   The Global Theory construction uses the matrix Gauss Sum mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumSingularAndInvertible.lean#L8-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumSingularAndInvertible.lean#L8-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
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

theorem GlobalTheory.matrixGaussSum_mul_unit (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type)
    [CommRing R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ) (a : Matrix (Fin r) (Fin r) k)
    (g : GL (Fin r) k) :
    (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
      ψ (Matrix.trace ((a * (g : Matrix (Fin r) (Fin r) k)) * (x : Matrix (Fin r) (Fin r) k)))) =
    ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) := by sorry
