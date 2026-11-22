-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_mul_le
-- name    : Lean4LPD.PauliString.weight_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:09.600816+00:00
-- url     : https://prove2.me/theorems/dfb6a57a-dd10-4c7b-ad2e-8078589bf2b8
-- title:
--   Pauli String: weight mul le
-- statement:
--   Without any hypothesis only `|G|` is available: the weight can move by up to the full weight of
--   `G` in either direction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L253-L256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L253-L256

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

theorem Lean4LPD.PauliString.weight_mul_le (G s : PauliString n) : weight (G * s) ≤ weight s + weight G := by sorry
