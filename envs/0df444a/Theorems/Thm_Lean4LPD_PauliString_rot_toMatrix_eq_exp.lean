-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_rot_toMatrix_eq_exp
-- name    : Lean4LPD.PauliString.rot_toMatrix_eq_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:11:10.158216+00:00
-- url     : https://prove2.me/theorems/b07c87a2-ace0-4eb8-b171-286124690694
-- title:
--   Pauli String: rot to Matrix eq exp
-- statement:
--   For every Hermitian Pauli string `G`, the closed-form rotation of its matrix is the genuine
--   matrix exponential `exp ((I * (θ/2)) • toMatrix G)`, the gate of
--   `apd:eq:pauli_rotation_branch`, in the entrywise `toMatrix` model. The product topology on
--   finite matrices supplies all analytic instances without choosing a norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L143-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L143-L146

module
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_RotationExp
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open scoped Nat
open Lean4LPD.PauliString
variable {n : ℕ} {G : PauliString n}

theorem Lean4LPD.PauliString.rot_toMatrix_eq_exp (hG : IsSelfAdjoint G) (θ : ℝ) :
    rot (toMatrix G) θ =
      NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix G) := by sorry
