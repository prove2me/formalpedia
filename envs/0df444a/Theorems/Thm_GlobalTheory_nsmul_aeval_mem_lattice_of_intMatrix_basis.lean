-- Prove2me | Theorems.Thm_GlobalTheory_nsmul_aeval_mem_lattice_of_intMatrix_basis
-- name    : GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix_basis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:40.52081+00:00
-- url     : https://prove2.me/theorems/ae9a23eb-10bf-4af5-b3a3-144a2d111d28
-- title:
--   Global Theory: nsmul aeval mem lattice of int Matrix basis
-- statement:
--   The Global Theory construction uses the nsmul aeval mem lattice of int Matrix basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NsmulAevalMemLatticeOfIntRationalMatrix.lean#L6-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NsmulAevalMemLatticeOfIntRationalMatrix.lean#L6-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NsmulAevalMemLatticeOfIntRationalMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix_basis (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (p : Polynomial ℚ) (D : ℕ) (hD : ∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) :
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by sorry
