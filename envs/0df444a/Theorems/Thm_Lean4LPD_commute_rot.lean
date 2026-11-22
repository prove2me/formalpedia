-- Prove2me | Theorems.Thm_Lean4LPD_commute_rot
-- name    : Lean4LPD.commute_rot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:39.24819+00:00
-- url     : https://prove2.me/theorems/0f748589-75de-4c36-a9e6-702e94a20b5d
-- title:
--   Lean4 LPD: commute rot
-- statement:
--   A rotation commutes with everything its generator commutes with: `rot` is a linear
--   combination of `1` and `G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L152-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L152-L153

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

theorem Lean4LPD.commute_rot (h : Commute G P) : Commute (rot G θ) P := by sorry
