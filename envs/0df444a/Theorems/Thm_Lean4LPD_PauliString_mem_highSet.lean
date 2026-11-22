-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_mem_highSet
-- name    : Lean4LPD.PauliString.mem_highSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:37.193403+00:00
-- url     : https://prove2.me/theorems/0dd9709a-31f5-4fe8-a4d3-4984016e1e65
-- title:
--   Pauli String: mem high Set
-- statement:
--   The Pauli String construction uses the mem high Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L428-L429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L428-L429

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.mem_highSet {n w : ℕ} {p : PauliIndex n} : p ∈ highSet n w ↔ w < wt p := by sorry
