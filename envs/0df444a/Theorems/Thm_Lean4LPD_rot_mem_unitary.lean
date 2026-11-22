-- Prove2me | Theorems.Thm_Lean4LPD_rot_mem_unitary
-- name    : Lean4LPD.rot_mem_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:40.880652+00:00
-- url     : https://prove2.me/theorems/f6dafa4f-f238-4590-8a04-2ba752ec3933
-- title:
--   Lean4 LPD: rot mem unitary
-- statement:
--   A rotation with a self-adjoint involutive generator is **unitary**. Since `unitary A` is a
--   submonoid, any finite product of rotations is unitary for free — including the paper's product
--   `U_g := ∏_{l ≤ g} e^{-i G_l dt/2}` of `apd:thm:local_flow_k_local`, which in this file's
--   convention is `∏ rot G_l (-dt)`, not `∏ rot G_l dt`: `rot G θ` is the `+` exponential.
--
--   This is unitarity only. The invariance of the Pauli 2-norm under conjugation (the `reservoir`
--   field of `Lean4LPD.Ladder`, used in the base case of `apd:cor:norm_cumulation_jump`) is a
--   statement about a norm this file deliberately does not carry; for Pauli rotations it is
--   `pauliNorm_conj` in `Pauli/Flow.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L216-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Rotation.lean#L216-L219

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

theorem Lean4LPD.rot_mem_unitary (hG₂ : G * G = 1) (hG : star G = G) : rot G θ ∈ unitary A := by sorry
