-- Prove2me | Theorems.Thm_Lean4LPD_exp_term_odd_of_involution
-- name    : Lean4LPD.exp_term_odd_of_involution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:06.276735+00:00
-- url     : https://prove2.me/theorems/b51d2f2b-092b-46e4-ade8-23beee29ba48
-- title:
--   Lean4 LPD: exp term odd of involution
-- statement:
--   The odd terms of the exponential series of `(z * I) • G` are scalar multiples of `G` when
--   `G * G = 1`: they are `I` times the terms of the sine series of `z`. There is no division by the
--   angle, so the zero-angle case needs no separate argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L67-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/RotationExp.lean#L67-L74

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

theorem Lean4LPD.exp_term_odd_of_involution (hG : G * G = 1) (z : ℂ) (n : ℕ) :
    ((2 * n + 1)!⁻¹ : ℂ) • ((z * Complex.I) • G) ^ (2 * n + 1) =
      (((z * Complex.I) ^ (2 * n + 1) / (2 * n + 1)! / Complex.I) * Complex.I) • G := by sorry
