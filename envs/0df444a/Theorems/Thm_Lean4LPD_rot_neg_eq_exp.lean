-- Prove2me | Theorems.Thm_Lean4LPD_rot_neg_eq_exp
-- name    : Lean4LPD.rot_neg_eq_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:27.146795+00:00
-- url     : https://prove2.me/theorems/9824a1da-8274-42cd-9e45-7016061e5910
-- title:
--   Lean4 LPD: rot neg eq exp
-- statement:
--   The negative-exponent gate `e^{-i G θ/2}` of `apd:eq:pauli_rotation_branch` is the
--   negative-angle rotation `rot G (-θ)`, not `rot G θ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L108-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L108-L110

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

theorem Lean4LPD.rot_neg_eq_exp (hG : G * G = 1) (θ : ℝ) :
    rot G (-θ) = NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) := by sorry
