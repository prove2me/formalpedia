-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_two_mul_yPhase
-- name    : Lean4LPD.PauliString.two_mul_yPhase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:16.736806+00:00
-- url     : https://prove2.me/theorems/e96e561e-5dc5-4739-a4c7-8f364977a89c
-- title:
--   Pauli String: two mul y Phase
-- statement:
--   Doubling the full Y-count phase gives the symplectic sign. This verifies the
--   Hermiticity convention for the positive tensor basis of `def:pauli_basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L226-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L226-L237

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.two_mul_yPhase : ∀ {n : ℕ} (x z : Bits n),
    2 * yPhase x z = signPhase (z ⬝ᵥ x) := by sorry
