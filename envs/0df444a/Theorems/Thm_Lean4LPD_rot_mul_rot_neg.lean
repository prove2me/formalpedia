-- Prove2me | Theorems.Thm_Lean4LPD_rot_mul_rot_neg
-- name    : Lean4LPD.rot_mul_rot_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:26.369069+00:00
-- url     : https://prove2.me/theorems/83c3d4b3-ea6e-4c06-8ea4-1890508996fa
-- title:
--   Lean4 LPD: rot mul rot neg
-- statement:
--   `rot G (-θ)` is a right inverse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L143-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L143-L144

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

theorem Lean4LPD.rot_mul_rot_neg (hG : G * G = 1) : rot G θ * rot G (-θ) = 1 := by sorry
