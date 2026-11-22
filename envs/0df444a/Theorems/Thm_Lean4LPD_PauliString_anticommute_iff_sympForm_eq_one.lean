-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_anticommute_iff_sympForm_eq_one
-- name    : Lean4LPD.PauliString.anticommute_iff_sympForm_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:28.019719+00:00
-- url     : https://prove2.me/theorems/b971564b-0ab0-4064-b028-d3aaf134c3b3
-- title:
--   Pauli String: anticommute iff symp Form eq one
-- statement:
--   Two Pauli strings anticommute exactly when the symplectic form is one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L363-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L363-L366

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

theorem Lean4LPD.PauliString.anticommute_iff_sympForm_eq_one (s t : PauliString n) :
    s * t = phaseMul 2 (t * s) ↔ sympForm s t = 1 := by sorry
