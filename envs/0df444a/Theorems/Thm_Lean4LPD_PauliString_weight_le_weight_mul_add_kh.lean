-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add_kh
-- name    : Lean4LPD.PauliString.weight_le_weight_mul_add_kh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:29.711739+00:00
-- url     : https://prove2.me/theorems/cc48ff5e-3964-4a0d-b3e6-737aae6d48e6
-- title:
--   Pauli String: weight le weight mul add kh
-- statement:
--   `|s| ≤ |G s| + (k_h - 1)` for `|G| ≤ k_h`: the lower bound on the partner's weight used in
--   the proof of `apd:thm:local_flow_k_local`, in additive form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L336-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L336-L339

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

theorem Lean4LPD.PauliString.weight_le_weight_mul_add_kh (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s ≤ weight (G * s) + (kh - 1) := by sorry
