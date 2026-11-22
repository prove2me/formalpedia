-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_exists_commuting_weight_increase_by_full_weight
-- name    : Lean4LPD.PauliString.exists_commuting_weight_increase_by_full_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:13.227709+00:00
-- url     : https://prove2.me/theorems/e2df538a-5077-4fbd-9bfc-2ef846523e92
-- title:
--   Pauli String: exists commuting weight increase by full weight
-- statement:
--   **The anticommutation hypothesis cannot be dropped.** For the *commuting* pair `G = X₁X₂`,
--   `s = Z₃` on three qubits, the supports are disjoint, so `|G s| = 3 = |s| + |G|` and the sharp
--   bound `|G s| ≤ |s| + (|G| - 1) = 2` fails.
--
--   This is why `weight_mul_le_weight_add` carries `sympForm G s = 1` and why the general statement
--   `weight_mul_le` is the best available without it. It is also why "a `k_h`-local rotation
--   increases the weight by at most `k_h - 1`" is a statement about *anticommuting* rotations. A
--   commuting rotation leaves the Pauli operator unchanged (`pauli_rotation_branch_commute` in
--   `Pauli/Branch.lean`), so the bare product `G s` never arises in that branch and its weight is
--   irrelevant there.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L275-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L275-L278

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

theorem Lean4LPD.PauliString.exists_commuting_weight_increase_by_full_weight :
    ∃ G s : PauliString 3,
      sympForm G s = 0 ∧ weight G = 2 ∧ weight s = 1 ∧ weight (G * s) = 3 := by sorry
