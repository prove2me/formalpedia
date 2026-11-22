-- Prove2me | Theorems.Thm_Lean4LPD_rot_eq_exp
-- name    : Lean4LPD.rot_eq_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:30.650459+00:00
-- url     : https://prove2.me/theorems/47422b26-9a33-499a-a7dd-9ed6105eae71
-- title:
--   Lean4 LPD: rot eq exp
-- statement:
--   **The closed-form rotation is the genuine exponential gate**: for `G * G = 1`,
--   `rot G θ = exp ((I * (θ/2)) • G)`. The sign is positive and the angle is halved, which is the
--   factor standing on the left of the Heisenberg conjugation in `apd:eq:pauli_rotation_branch`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L102-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L102-L104

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}
variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]

theorem Lean4LPD.rot_eq_exp (hG : G * G = 1) (θ : ℝ) :
    rot G θ = NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) := by sorry
