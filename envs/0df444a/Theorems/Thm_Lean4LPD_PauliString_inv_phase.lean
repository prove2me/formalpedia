-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_inv_phase
-- name    : Lean4LPD.PauliString.inv_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:07.703589+00:00
-- url     : https://prove2.me/theorems/40e0633b-bc1a-431f-869b-37f443f923a2
-- title:
--   Pauli String: inv phase
-- statement:
--   The Pauli String construction uses the inv phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L209-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L209-L210

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

theorem Lean4LPD.PauliString.inv_phase (s : PauliString n) :
    s⁻¹.phase = -s.phase + signPhase (s.z ⬝ᵥ s.x) := by sorry
