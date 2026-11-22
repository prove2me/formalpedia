-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add
-- name    : Lean4LPD.PauliString.weight_le_weight_mul_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:12.192889+00:00
-- url     : https://prove2.me/theorems/ba894306-1188-4203-bcba-2d9ab7da93a0
-- title:
--   Pauli String: weight le weight mul add
-- statement:
--   **The lower half**, `|G s| ≥ |s| - (|G| - 1)` in the form that avoids truncated subtraction.
--   This is the direction the proof of `apd:thm:local_flow_k_local` uses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L298-L302
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L298-L302

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}

theorem Lean4LPD.PauliString.weight_le_weight_mul_add (h : sympForm G s = 1) :
    weight s ≤ weight (G * s) + (weight G - 1) := by sorry
