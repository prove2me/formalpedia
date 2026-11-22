-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
-- name    : Lean4LPD.PauliString.sympForm_phaseMul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:00.619891+00:00
-- url     : https://prove2.me/theorems/0049750d-6c95-4bbf-91d1-8dd58d75a36b
-- title:
--   Pauli String: symp Form phase Mul left
-- statement:
--   The Pauli String construction uses the symp Form phase Mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L303-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L303-L304

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

theorem Lean4LPD.PauliString.sympForm_phaseMul_left (k : ZMod 4) (s t : PauliString n) :
    sympForm (phaseMul k s) t = sympForm s t := by sorry

attribute [defeq] Lean4LPD.PauliString.sympForm_phaseMul_left
