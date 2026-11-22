-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_star_mul_z
-- name    : Lean4LPD.PauliString.star_mul_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:55.78256+00:00
-- url     : https://prove2.me/theorems/fe567e4b-dc8a-4518-8b14-8302af812f55
-- title:
--   Pauli String: star mul z
-- statement:
--   The Pauli String construction uses the star mul z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L172-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L172-L172

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}

theorem Lean4LPD.PauliString.star_mul_z (s t : PauliString n) : (star s * t).z = s.z + t.z := by sorry
