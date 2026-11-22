-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_truncOp_univ
-- name    : Lean4LPD.PauliString.truncOp_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:45.132411+00:00
-- url     : https://prove2.me/theorems/4cc24232-b2ce-44c5-9c25-9ab519b447d3
-- title:
--   Pauli String: trunc Op univ
-- statement:
--   **Completeness of the Pauli expansion**: `O = ∑_P x_P P`, the expansion from which the proof
--   of `apd:thm:local_flow_k_local` starts and the companion of Parseval in `Pauli/Coeff.lean`.
--
--   Proved from Parseval, not from a dimension count. `sum_norm_coeff_sq` says
--   `∑_p ‖x_p‖² = ‖O‖_{2,normalized}²`, so an operator all of whose coefficients vanish has
--   `‖·‖_{2,normalized} = 0`, hence all
--   entries zero; `coeff_truncOp` says the difference `∑_p x_p P_p − O` is such an operator. No
--   `InnerProductSpace` instance on `Matrix` and no `finrank` count is involved.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L162-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean#L162-L181

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

theorem Lean4LPD.PauliString.truncOp_univ (O : Matrix (Bits n) (Bits n) ℂ) : truncOp univ O = O := by sorry
