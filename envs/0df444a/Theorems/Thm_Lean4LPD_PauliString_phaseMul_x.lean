-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
-- name    : Lean4LPD.PauliString.phaseMul_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:57:56.603092+00:00
-- url     : https://prove2.me/theorems/959e1f2e-dda8-447e-84e6-154a8dea4bd9
-- title:
--   Pauli String: phase Mul x
-- statement:
--   The Pauli String construction uses the phase Mul x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L295-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L295-L295

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

theorem Lean4LPD.PauliString.phaseMul_x (k : ZMod 4) (s : PauliString n) : (phaseMul k s).x = s.x := by sorry

attribute [defeq] Lean4LPD.PauliString.phaseMul_x
