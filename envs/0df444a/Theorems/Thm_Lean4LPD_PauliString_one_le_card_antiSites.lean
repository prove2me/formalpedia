-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_one_le_card_antiSites
-- name    : Lean4LPD.PauliString.one_le_card_antiSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:54.687766+00:00
-- url     : https://prove2.me/theorems/77928329-cc2d-4063-b49c-f303dc952ce7
-- title:
--   Pauli String: one le card anti Sites
-- statement:
--   Anticommuting Pauli strings share at least one site at which they locally anticommute.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L237-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L237-L241

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

theorem Lean4LPD.PauliString.one_le_card_antiSites (h : sympForm G s = 1) : 1 ≤ (antiSites G s).card := by sorry
