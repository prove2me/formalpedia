-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
-- name    : Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:01.246326+00:00
-- url     : https://prove2.me/theorems/d574f75d-a368-4e32-a797-c925e2a8ab4e
-- title:
--   Pauli String: phase Mul eq phase Mul iff
-- statement:
--   The Pauli String construction uses the phase Mul eq phase Mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L319-L325
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L319-L325

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

theorem Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff {k l : ZMod 4} {s : PauliString n} :
    phaseMul k s = phaseMul l s ↔ k = l := by sorry
