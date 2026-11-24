-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_real_coordinate_basis
-- name    : GlobalTheory.T.lattice_real_coordinate_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:56.18128+00:00
-- url     : https://prove2.me/theorems/bc2a64a1-7417-4107-b24b-98cb733824ba
-- title:
--   T: lattice real coordinate basis
-- statement:
--   The T construction uses the lattice real coordinate basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeRealCoordinateBasisStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeRealCoordinateBasisStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeRealCoordinateBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeRealCoordinateBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_real_coordinate_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by sorry
