-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_phaseMul_one_X1_mul_Z1
-- name    : Lean4LPD.PauliString.phaseMul_one_X1_mul_Z1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:08:42.718124+00:00
-- url     : https://prove2.me/theorems/8e4dd84d-1242-43dc-b0c8-7760d43f1749
-- title:
--   Pauli String: phase Mul one X1 mul Z1
-- statement:
--   `i` times their product is the Hermitian partner `Y`, as `isSelfAdjoint_phaseMul_one_mul`
--   predicts. The bare product is not: `X Z = −i Y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L482-L482
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L482-L482

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

theorem Lean4LPD.PauliString.phaseMul_one_X1_mul_Z1 : phaseMul 1 (X1 * Z1) = Y1 := by sorry
