-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_commute_iff_sympForm_eq_zero
-- name    : Lean4LPD.PauliString.commute_iff_sympForm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:26.989392+00:00
-- url     : https://prove2.me/theorems/b2385841-1454-457d-a604-9d4f5b4cd636
-- title:
--   Pauli String: commute iff symp Form eq zero
-- statement:
--   Two Pauli strings commute exactly when the symplectic form vanishes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L352-L360
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L352-L360

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

theorem Lean4LPD.PauliString.commute_iff_sympForm_eq_zero (s t : PauliString n) :
    Commute s t ↔ sympForm s t = 0 := by sorry
