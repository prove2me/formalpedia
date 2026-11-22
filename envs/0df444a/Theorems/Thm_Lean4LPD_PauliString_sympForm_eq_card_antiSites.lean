-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_card_antiSites
-- name    : Lean4LPD.PauliString.sympForm_eq_card_antiSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:25.402864+00:00
-- url     : https://prove2.me/theorems/be71956e-cdc3-4573-9c1c-706a651a49ee
-- title:
--   Pauli String: symp Form eq card anti Sites
-- statement:
--   **`⟪G,s⟫` is `#antiSites` modulo two.** This is what turns a parity statement into a counting
--   statement, and it is the whole source of the `-1` in `|G s| ≥ |s| - (k_h - 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L227-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L227-L234

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}

theorem Lean4LPD.PauliString.sympForm_eq_card_antiSites (G s : PauliString n) :
    sympForm G s = ((antiSites G s).card : ZMod 2) := by sorry
