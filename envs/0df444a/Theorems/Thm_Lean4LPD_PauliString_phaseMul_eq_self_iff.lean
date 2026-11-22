-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
-- name    : Lean4LPD.PauliString.phaseMul_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:00.747499+00:00
-- url     : https://prove2.me/theorems/7a21113f-02ac-4916-9d33-8fa5471d50dd
-- title:
--   Pauli String: phase Mul eq self iff
-- statement:
--   The Pauli String construction uses the phase Mul eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L327-L333
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L327-L333

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

theorem Lean4LPD.PauliString.phaseMul_eq_self_iff {k : ZMod 4} {s : PauliString n} :
    phaseMul k s = s ↔ k = 0 := by sorry
