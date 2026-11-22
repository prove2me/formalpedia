-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeff_ext
-- name    : Lean4LPD.PauliString.coeff_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:16.843859+00:00
-- url     : https://prove2.me/theorems/0a31ef7a-0c37-4ee0-942f-a4373e2e0e82
-- title:
--   Pauli String: coeff ext
-- statement:
--   Equality of every Pauli coefficient determines an operator. This is the completeness helper
--   used to identify the discarded operator in `apd:eq:step_component`, rather
--   than merely matching a scalar norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L69-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L69-L76

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.coeff_ext {A B : Matrix (Bits n) (Bits n) ℂ}
    (h : ∀ p : PauliIndex n, coeff A p = coeff B p) : A = B := by sorry
