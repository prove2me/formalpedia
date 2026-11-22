-- Prove2me | Theorems.Thm_Lean4LPD_bits_add_eq_zero_iff
-- name    : Lean4LPD.bits_add_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:29.100131+00:00
-- url     : https://prove2.me/theorems/5669f459-989b-4d13-ad48-fe1259806bec
-- title:
--   Lean4 LPD: bits add eq zero iff
-- statement:
--   In characteristic two, `u + v = 0` says `u = v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L142-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L142-L147

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

theorem Lean4LPD.bits_add_eq_zero_iff {n : ℕ} {u v : Fin n → ZMod 2} : u + v = 0 ↔ u = v := by sorry
