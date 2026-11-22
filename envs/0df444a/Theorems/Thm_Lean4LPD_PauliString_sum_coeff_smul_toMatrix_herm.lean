-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sum_coeff_smul_toMatrix_herm
-- name    : Lean4LPD.PauliString.sum_coeff_smul_toMatrix_herm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:31.605841+00:00
-- url     : https://prove2.me/theorems/a870c6d5-928f-43d9-9ce5-8dca5a51f635
-- title:
--   Pauli String: sum coeff smul to Matrix herm
-- statement:
--   **The Pauli expansion** `O = ∑_P x_P P` in its usual form: the same statement as
--   `truncOp_univ`, written without the truncation operator. The basis operators are the
--   self-adjoint representatives `toMatrix (herm p)`; `Pauli/Tensor.lean` identifies them with the
--   correctly phased tensor products of one-qubit Pauli matrices (`herm p` is not always the tensor
--   product with coefficient `+1`; it can differ from it by a sign).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L188-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L188-L189

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n ko kh : ℕ}

theorem Lean4LPD.PauliString.sum_coeff_smul_toMatrix_herm (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ p : PauliIndex n, coeff O p • toMatrix (herm p) = O := by sorry
