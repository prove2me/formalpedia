-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_sum
-- name    : Lean4LPD.PauliString.sympForm_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:22.50095+00:00
-- url     : https://prove2.me/theorems/a3cc3151-1041-46c2-b4a3-e88702a339c7
-- title:
--   Pauli String: symp Form eq sum
-- statement:
--   The Pauli String construction uses the symp Form eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L266-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L266-L268

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

theorem Lean4LPD.PauliString.sympForm_eq_sum (s t : PauliString n) :
    sympForm s t = ∑ i, (s.x i * t.z i + s.z i * t.x i) := by sorry
