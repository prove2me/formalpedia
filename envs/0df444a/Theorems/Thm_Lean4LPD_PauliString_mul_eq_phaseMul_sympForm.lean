-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mul_eq_phaseMul_sympForm
-- name    : Lean4LPD.PauliString.mul_eq_phaseMul_sympForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:16.434799+00:00
-- url     : https://prove2.me/theorems/bd47f0e5-a6bf-44cb-82c4-7b396f08e119
-- title:
--   Pauli String: mul eq phase Mul symp Form
-- statement:
--   **The exact commutation law.** Reversing a product multiplies it by `(-1)^{⟪s,t⟫}`. The two
--   cases of `apd:eq:pauli_rotation_branch`, commuting and anticommuting, are the two values of this
--   one sign.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L338-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L338-L349

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}

theorem Lean4LPD.PauliString.mul_eq_phaseMul_sympForm (s t : PauliString n) :
    s * t = phaseMul (signPhase (sympForm s t)) (t * s) := by sorry
