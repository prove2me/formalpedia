-- Prove2me | Theorems.Thm_GlobalTheory_exists_gl_det_eq_mul_eq_of_det_eq_zero
-- name    : GlobalTheory.exists_gl_det_eq_mul_eq_of_det_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:55:04.5572+00:00
-- url     : https://prove2.me/theorems/a1e6b000-4902-4783-9ecd-364ea89eeced
-- title:
--   Global Theory: exists gl det eq mul eq of det eq zero
-- statement:
--   The Global Theory construction uses the exists gl det eq mul eq of det eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumSingularAndInvertible.lean#L32-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumSingularAndInvertible.lean#L32-L51

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

theorem GlobalTheory.exists_gl_det_eq_mul_eq_of_det_eq_zero (k : Type) [Field k] (r : ℕ)
    (a : Matrix (Fin r) (Fin r) k) (ha : a.det = 0) (t : kˣ) :
    ∃ g : GL (Fin r) k, Matrix.GeneralLinearGroup.det g = t ∧
      a * (g : Matrix (Fin r) (Fin r) k) = a := by sorry
