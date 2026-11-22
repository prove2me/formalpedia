-- Prove2me | Theorems.Thm_Lean4LPD_rot_conj_of_commute
-- name    : Lean4LPD.rot_conj_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:29.350555+00:00
-- url     : https://prove2.me/theorems/4fa2a4e8-188b-40e5-bc10-dc7e3a0ddffe
-- title:
--   Lean4 LPD: rot conj of commute
-- statement:
--   **Commuting branch** of `apd:eq:pauli_rotation_branch`: a rotation whose
--   generator commutes with `P` leaves `P` alone. No weight change, no new Pauli.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L157-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L157-L159

module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}

theorem Lean4LPD.rot_conj_of_commute (hG : G * G = 1) (h : Commute G P) :
    rot G θ * P * rot G (-θ) = P := by sorry
