-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_phase_sub_of_isSelfAdjoint
-- name    : Lean4LPD.PauliString.phase_sub_of_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:35.45553+00:00
-- url     : https://prove2.me/theorems/af75a2fc-acb3-4dc7-a184-a56118118107
-- title:
--   Pauli String: phase sub of is Self Adjoint
-- statement:
--   Two self-adjoint Pauli strings on the same class differ by at most a sign: their phases
--   differ by `0` or `2`. This is the residual freedom `isSelfAdjoint_iff_phase` leaves.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L139-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L139-L148

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

theorem Lean4LPD.PauliString.phase_sub_of_isSelfAdjoint {s t : PauliString n} (hs : IsSelfAdjoint s)
    (ht : IsSelfAdjoint t) (hx : s.x = t.x) (hz : s.z = t.z) :
    s.phase - t.phase = 0 ∨ s.phase - t.phase = 2 := by sorry
