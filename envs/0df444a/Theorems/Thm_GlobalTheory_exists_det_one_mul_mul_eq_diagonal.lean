-- Prove2me | Theorems.Thm_GlobalTheory_exists_det_one_mul_mul_eq_diagonal
-- name    : GlobalTheory.exists_det_one_mul_mul_eq_diagonal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:14.789818+00:00
-- url     : https://prove2.me/theorems/57ae703f-f47f-49af-a083-3017f4a55d0b
-- title:
--   Global Theory: exists det one mul mul eq diagonal
-- statement:
--   The Global Theory construction uses the exists det one mul mul eq diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZero.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZero.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.exists_det_one_mul_mul_eq_diagonal {K : Type} [Field K] {a : ℕ}
    (A : Matrix (Fin a) (Fin a) K) :
    ∃ (P Q : Matrix (Fin a) (Fin a) K) (D : Fin a → K),
      P.det = 1 ∧ Q.det = 1 ∧ P * A * Q = Matrix.diagonal D := by sorry
