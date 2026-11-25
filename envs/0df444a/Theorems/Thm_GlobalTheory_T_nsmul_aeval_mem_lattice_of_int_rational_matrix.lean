-- Prove2me | Theorems.Thm_GlobalTheory_T_nsmul_aeval_mem_lattice_of_int_rational_matrix
-- name    : GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:01.814125+00:00
-- url     : https://prove2.me/theorems/63d5e37d-5dc0-4411-aeca-894a52001320
-- title:
--   T: nsmul aeval mem lattice of int rational matrix
-- statement:
--   The T construction uses the nsmul aeval mem lattice of int rational matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NsmulAevalMemLatticeOfIntRationalMatrixStatement.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NsmulAevalMemLatticeOfIntRationalMatrixStatement.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NsmulAevalMemLatticeOfIntRationalMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NsmulAevalMemLatticeOfIntRationalMatrixStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by sorry
