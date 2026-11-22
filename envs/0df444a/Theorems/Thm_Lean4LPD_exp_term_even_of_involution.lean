-- Prove2me | Theorems.Thm_Lean4LPD_exp_term_even_of_involution
-- name    : Lean4LPD.exp_term_even_of_involution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:04.66666+00:00
-- url     : https://prove2.me/theorems/e9702513-2974-4ae9-ab91-c4faa8c0100e
-- title:
--   Lean4 LPD: exp term even of involution
-- statement:
--   The even terms of the exponential series of `(z * I) • G` are scalar multiples of `1` when
--   `G * G = 1`: they are the terms of the cosine series of `z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L56-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L56-L62

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

theorem Lean4LPD.exp_term_even_of_involution (hG : G * G = 1) (z : ℂ) (n : ℕ) :
    ((2 * n)!⁻¹ : ℂ) • ((z * Complex.I) • G) ^ (2 * n) =
      ((z * Complex.I) ^ (2 * n) / (2 * n)!) • (1 : A) := by sorry
