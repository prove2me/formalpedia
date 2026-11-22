-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeff_add
-- name    : Lean4LPD.PauliString.coeff_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:11.401253+00:00
-- url     : https://prove2.me/theorems/c5256d37-2624-49c5-9289-59c3b00d21d3
-- title:
--   Pauli String: coeff add
-- statement:
--   Coefficients are additive, the coefficient-space helper for the triangle inequality in
--   `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L59-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L59-L61

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.coeff_add (A B : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    coeff (A + B) p = coeff A p + coeff B p := by sorry
