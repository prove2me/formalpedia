-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_bitsMatrixEquiv_star
-- name    : Lean4LPD.PauliString.bitsMatrixEquiv_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:08.837662+00:00
-- url     : https://prove2.me/theorems/a49b342d-bb54-4957-9ab6-478131b985a4
-- title:
--   Pauli String: bits Matrix Equiv star
-- statement:
--   The change of computational-basis indexing preserves the adjoint as well as the algebra
--   operations (`def:pauli_basis`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L294-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L294-L295

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.bitsMatrixEquiv_star (n : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    bitsMatrixEquiv n (star A) = star (bitsMatrixEquiv n A) := by sorry
