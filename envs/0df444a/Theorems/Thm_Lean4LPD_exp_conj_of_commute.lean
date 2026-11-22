-- Prove2me | Theorems.Thm_Lean4LPD_exp_conj_of_commute
-- name    : Lean4LPD.exp_conj_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:10:51.94925+00:00
-- url     : https://prove2.me/theorems/2d05ef46-4fa9-47f3-aeba-f58fbe9809f5
-- title:
--   Lean4 LPD: exp conj of commute
-- statement:
--   The commuting branch of `apd:eq:pauli_rotation_branch`, stated with genuine exponentials
--   rather than the algebraic closed form: if `G * G = 1` and `G` commutes with `P`, conjugation by
--   `e^{i G θ/2}` leaves `P` unchanged. This is `rot_conj_of_commute` transported along
--   `rot_eq_exp`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L116-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L116-L120

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

theorem Lean4LPD.exp_conj_of_commute (hG : G * G = 1) (h : Commute G P) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) * P *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) = P := by sorry
