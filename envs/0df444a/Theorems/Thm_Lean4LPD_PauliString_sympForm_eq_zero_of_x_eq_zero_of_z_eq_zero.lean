-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero
-- name    : Lean4LPD.PauliString.sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:26.911041+00:00
-- url     : https://prove2.me/theorems/150e3f8b-47eb-4759-b360-b0553d1d30c4
-- title:
--   Pauli String: symp Form eq zero of x eq zero of z eq zero
-- statement:
--   A Pauli string with neither an `X`- nor a `Z`-part is a phase, and a phase commutes with
--   everything. Contrapositively: anything that anticommutes with some `t` has a non-trivial `X`- or
--   `Z`-part. No self-adjointness is involved.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L448-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L448-L450

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

theorem Lean4LPD.PauliString.sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero {s t : PauliString n}
    (hx : s.x = 0) (hz : s.z = 0) : sympForm s t = 0 := by sorry
