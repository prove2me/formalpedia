-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
-- name    : Lean4LPD.PauliString.sympForm_phaseMul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:57:58.274321+00:00
-- url     : https://prove2.me/theorems/00885f61-0b11-4a52-87c2-9b1e68da6dcf
-- title:
--   Pauli String: symp Form phase Mul right
-- statement:
--   The Pauli String construction uses the symp Form phase Mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L300-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L300-L301

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

theorem Lean4LPD.PauliString.sympForm_phaseMul_right (k : ZMod 4) (s t : PauliString n) :
    sympForm s (phaseMul k t) = sympForm s t := by sorry

attribute [defeq] Lean4LPD.PauliString.sympForm_phaseMul_right
