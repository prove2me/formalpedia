-- Prove2me | Theorems.Thm_GlobalTheory_matrixGaussSum_singular_and_invertible
-- name    : GlobalTheory.matrixGaussSum_singular_and_invertible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:47.637419+00:00
-- url     : https://prove2.me/theorems/d7893632-384c-406c-ae6d-71c4c2954c45
-- title:
--   Global Theory: matrix Gauss Sum singular and invertible
-- statement:
--   The Global Theory construction uses the matrix Gauss Sum singular and invertible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumSingularAndInvertible.lean#L53-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumSingularAndInvertible.lean#L53-L68

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

theorem GlobalTheory.matrixGaussSum_singular_and_invertible :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∀ a : Matrix (Fin r) (Fin r) k, a.det = 0 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) = 0) ∧ ∀ a : GL (Fin r) k, (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace ((a : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k)))) = ((ξ (Matrix.GeneralLinearGroup.det a) : Rˣ) : R) * (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) := by sorry
