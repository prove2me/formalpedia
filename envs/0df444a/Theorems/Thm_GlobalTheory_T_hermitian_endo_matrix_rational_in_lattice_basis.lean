-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_endo_matrix_rational_in_lattice_basis
-- name    : GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:08.404925+00:00
-- url     : https://prove2.me/theorems/5c7d3a0f-6902-5079-a7c7-3eec82a34237
-- title:
--   T: hermitian endo matrix rational in lattice basis
-- statement:
--   The T construction uses the hermitian endo matrix rational in lattice basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianEndoMatrixRationalInLatticeBasisStatement.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianEndoMatrixRationalInLatticeBasisStatement.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianEndoMatrixRationalInLatticeBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianEndoMatrixRationalInLatticeBasisStatement
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

theorem GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by sorry
