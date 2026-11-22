-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
-- name    : Lean4LPD.PauliString.phaseMul_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:57:59.558841+00:00
-- url     : https://prove2.me/theorems/30cbbc84-ecf1-4729-a97f-26ecb3dc819c
-- title:
--   Pauli String: phase Mul z
-- statement:
--   The Pauli String construction uses the phase Mul z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L296-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L296-L296

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

theorem Lean4LPD.PauliString.phaseMul_z (k : ZMod 4) (s : PauliString n) : (phaseMul k s).z = s.z := by sorry

attribute [defeq] Lean4LPD.PauliString.phaseMul_z
