-- Prove2me | Theorems.Thm_Lean4LPD_exp_conj_of_anticommute
-- name    : Lean4LPD.exp_conj_of_anticommute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:10:51.622547+00:00
-- url     : https://prove2.me/theorems/77f80ee7-9a74-4f0c-9a18-afc7a160aa80
-- title:
--   Lean4 LPD: exp conj of anticommute
-- statement:
--   The anticommuting branch of `apd:eq:pauli_rotation_branch`, stated with genuine
--   exponentials: if `G * G = 1` and `G * P = -(P * G)`, conjugation by `e^{i G θ/2}` sends `P` to
--   `cos θ • P + (I * sin θ) • (G * P)`. The conjugation angle is `θ`, not `θ/2`, and the partner is
--   `G * P`. This is `rot_conj_of_anticommute` transported along `rot_eq_exp`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L126-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L126-L131

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

theorem Lean4LPD.exp_conj_of_anticommute (hG : G * G = 1) (h : G * P = -(P * G)) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) * P *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) =
      (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) := by sorry
