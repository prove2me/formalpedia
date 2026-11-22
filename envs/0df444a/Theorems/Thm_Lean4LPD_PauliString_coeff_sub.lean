-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeff_sub
-- name    : Lean4LPD.PauliString.coeff_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:50.399398+00:00
-- url     : https://prove2.me/theorems/7b987ed2-89d0-466c-a3ce-e02ac2ff33ea
-- title:
--   Pauli String: coeff sub
-- statement:
--   Coefficients preserve operator subtraction, an algebraic helper for the discarded component
--   `(1 - Π_{≤ w*}) A` in `apd:eq:step_component`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L54-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L54-L56

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

theorem Lean4LPD.PauliString.coeff_sub (A B : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    coeff (A - B) p = coeff A p - coeff B p := by sorry
