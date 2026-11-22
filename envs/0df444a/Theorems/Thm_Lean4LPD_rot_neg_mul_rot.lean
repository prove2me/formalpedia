-- Prove2me | Theorems.Thm_Lean4LPD_rot_neg_mul_rot
-- name    : Lean4LPD.rot_neg_mul_rot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:39.448637+00:00
-- url     : https://prove2.me/theorems/5ef35b2c-1913-4485-bcef-afb7142f32fb
-- title:
--   Lean4 LPD: rot neg mul rot
-- statement:
--   `rot G (-θ)` is a left inverse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L147-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L147-L148

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

theorem Lean4LPD.rot_neg_mul_rot (hG : G * G = 1) : rot G (-θ) * rot G θ = 1 := by sorry
