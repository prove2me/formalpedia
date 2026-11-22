-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
-- name    : Lean4LPD.PauliString.coeffVec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:31.999816+00:00
-- url     : https://prove2.me/theorems/7550a3df-937d-4f0d-a763-952216dc1e44
-- title:
--   Pauli String: coeff Vec apply
-- statement:
--   The Pauli String construction uses the coeff Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L365-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L365-L366

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

theorem Lean4LPD.PauliString.coeffVec_apply (O : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    (coeffVec O).ofLp p = coeff O p := by sorry

attribute [defeq] Lean4LPD.PauliString.coeffVec_apply
