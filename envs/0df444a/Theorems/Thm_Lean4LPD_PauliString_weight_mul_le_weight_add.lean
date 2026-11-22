-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_mul_le_weight_add
-- name    : Lean4LPD.PauliString.weight_mul_le_weight_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:23.277797+00:00
-- url     : https://prove2.me/theorems/bffdf69d-87cd-4687-a8a7-24587bd4ef33
-- title:
--   Pauli String: weight mul le weight add
-- statement:
--   **The upper half**, `|G s| ≤ |s| + (|G| - 1)`. This is the direction behind the rung spacing
--   `w_m = k_o + (m-1)(k_h-1)`: applied `m - 1` times, it bounds by `w_m` the weight reachable from
--   weight `k_o` by anticommuting `k_h`-local rotations. That `w_m` is *attained* is not
--   formalized.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L308-L312
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L308-L312

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

theorem Lean4LPD.PauliString.weight_mul_le_weight_add (h : sympForm G s = 1) :
    weight (G * s) ≤ weight s + (weight G - 1) := by sorry
