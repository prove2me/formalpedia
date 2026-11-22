-- Prove2me | Theorems.Thm_Lean4LPD_star_rot
-- name    : Lean4LPD.star_rot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:38.468041+00:00
-- url     : https://prove2.me/theorems/90f070be-1956-4fe5-8e43-4b2cdb8b1872
-- title:
--   Lean4 LPD: star rot
-- statement:
--   Adjoining a rotation reverses its angle, when the generator is self-adjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L201-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L201-L205

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
variable [StarRing A] [StarModule ℂ A]

theorem Lean4LPD.star_rot (hG : star G = G) : star (rot G θ) = rot G (-θ) := by sorry
