-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_anticommute
-- name    : Lean4LPD.PauliString.pauli_rotation_branch_anticommute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:41.582904+00:00
-- url     : https://prove2.me/theorems/24dd284c-f7b0-4761-836c-e13ae63c1fe3
-- title:
--   Pauli String: pauli rotation branch anticommute
-- statement:
--   The anticommuting branch: if `⟪G,s⟫ = 1`, the image has **two terms, the new one `G s`
--   carrying `i sin(θ)`**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L144-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L144-L147

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

theorem Lean4LPD.PauliString.pauli_rotation_branch_anticommute (hG : IsSelfAdjoint G) (h : sympForm G s = 1) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • toMatrix (G * s) := by sorry
