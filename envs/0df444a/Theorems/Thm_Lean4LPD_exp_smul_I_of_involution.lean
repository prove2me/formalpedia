-- Prove2me | Theorems.Thm_Lean4LPD_exp_smul_I_of_involution
-- name    : Lean4LPD.exp_smul_I_of_involution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:08.608819+00:00
-- url     : https://prove2.me/theorems/7caa2b0f-8819-42b9-9cc5-1e2f86c03d94
-- title:
--   Lean4 LPD: exp smul I of involution
-- statement:
--   **The exponential of an involution**, for a complex angle `z`: if `G * G = 1` then
--   `exp ((I * z) • G) = cos z • 1 + (I * sin z) • G`. This is the gate identity underlying
--   `apd:eq:pauli_rotation_branch`, proved by summing the even and odd subsequences of Mathlib's
--   exponential series (`HasSum.even_add_odd`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L82-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L82-L97

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

theorem Lean4LPD.exp_smul_I_of_involution (hG : G * G = 1) (z : ℂ) :
    NormedSpace.exp ((Complex.I * z) • G) =
      Complex.cos z • (1 : A) + (Complex.I * Complex.sin z) • G := by sorry
