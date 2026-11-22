-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
-- name    : Lean4LPD.PauliString.pauliNorm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:26.950504+00:00
-- url     : https://prove2.me/theorems/bc8ed38b-fcc9-4e5a-b454-c738b7fb7ca1
-- title:
--   Pauli String: pauli Norm sq
-- statement:
--   The Pauli String construction uses the pauli Norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L197-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L197-L198

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

theorem Lean4LPD.PauliString.pauliNorm_sq (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm O ^ 2 = pauliNormSq O := by sorry
