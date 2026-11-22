-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_mul_le_weight_add_kh
-- name    : Lean4LPD.PauliString.weight_mul_le_weight_add_kh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:33.908815+00:00
-- url     : https://prove2.me/theorems/9dae67e6-403f-435b-acf5-677866d42294
-- title:
--   Pauli String: weight mul le weight add kh
-- statement:
--   `|G s| ≤ |s| + (k_h - 1)` for `|G| ≤ k_h` — the direction that fixes the rung spacing
--   `w_m = k_o + (m-1)(k_h-1)` of `apd:thm:local_flow_k_local`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L362-L365
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L362-L365

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
variable {kh : ℕ}

theorem Lean4LPD.PauliString.weight_mul_le_weight_add_kh (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight (G * s) ≤ weight s + (kh - 1) := by sorry
