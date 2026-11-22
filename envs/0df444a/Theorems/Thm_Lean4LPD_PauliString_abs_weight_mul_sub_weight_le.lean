-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_abs_weight_mul_sub_weight_le
-- name    : Lean4LPD.PauliString.abs_weight_mul_sub_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:17.29682+00:00
-- url     : https://prove2.me/theorems/2bfdffdc-d333-4ffe-96b8-09dd284acf88
-- title:
--   Pauli String: abs weight mul sub weight le
-- statement:
--   **The two-sided weight bound**: an anticommuting generator of weight `|G|` changes the weight
--   of `s` by at most `|G| - 1`. Stated over `ℤ` so that no truncated subtraction is hiding in it.
--
--   The bound is in terms of the actual weight `|G|`, which is slightly stronger than the paper's
--   statement in terms of a locality parameter `k ≥ |G|` (the weight changes by at most `k - 1`, one
--   of the consequences drawn from `apd:eq:pauli_rotation_branch`). The parameterized forms are the
--   `k_h` corollaries `weight_sub_le_weight_mul` and `weight_mul_le_weight_add_kh` below, which follow
--   from the two halves above.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L322-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L322-L328

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

theorem Lean4LPD.PauliString.abs_weight_mul_sub_weight_le (h : sympForm G s = 1) :
    |(weight (G * s) : ℤ) - (weight s : ℤ)| ≤ (weight G : ℤ) - 1 := by sorry
