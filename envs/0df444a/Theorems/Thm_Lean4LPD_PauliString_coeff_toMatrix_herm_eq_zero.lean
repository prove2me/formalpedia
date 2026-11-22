-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeff_toMatrix_herm_eq_zero
-- name    : Lean4LPD.PauliString.coeff_toMatrix_herm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:12.315691+00:00
-- url     : https://prove2.me/theorems/f889306c-6646-4200-8e8d-1be11d30e2e8
-- title:
--   Pauli String: coeff to Matrix herm eq zero
-- statement:
--   A basis Pauli is `|q|`-local: no class of larger weight carries a coefficient.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L348-L352
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L348-L352

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.coeff_toMatrix_herm_eq_zero {p q : PauliIndex n} (h : wt q < wt p) :
    coeff (toMatrix (herm q)) p = 0 := by sorry
