-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_sub_le_weight_mul
-- name    : Lean4LPD.PauliString.weight_sub_le_weight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:21.830223+00:00
-- url     : https://prove2.me/theorems/4685b97d-88f8-4be8-8955-835e81a65af6
-- title:
--   Pauli String: weight sub le weight mul
-- statement:
--   **`|G s| ≥ |s| - (k_h - 1)`** — the same bound in subtractive form, which is where the proof
--   of `apd:thm:local_flow_k_local` places the partner Pauli one rung down rather than `k_h` rungs
--   down. The natural-number subtraction is harmless: when `|s| < k_h - 1` the left-hand side is `0`
--   and the bound is trivially true, and otherwise it is the additive form rearranged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L345-L348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L345-L348

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

theorem Lean4LPD.PauliString.weight_sub_le_weight_mul (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s - (kh - 1) ≤ weight (G * s) := by sorry
