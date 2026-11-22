-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_commute
-- name    : Lean4LPD.PauliString.pauli_rotation_branch_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:40.609879+00:00
-- url     : https://prove2.me/theorems/f64f55ae-b13e-421e-bb29-335e7ab30c92
-- title:
--   Pauli String: pauli rotation branch commute
-- statement:
--   The commuting branch: if `⟪G,s⟫ = 0`, **no rotation occurs and the Pauli operator is
--   unchanged**; in particular its weight does not change.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L138-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L138-L140

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}

theorem Lean4LPD.PauliString.pauli_rotation_branch_commute (hG : IsSelfAdjoint G) (h : sympForm G s = 0) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ) = toMatrix s := by sorry
