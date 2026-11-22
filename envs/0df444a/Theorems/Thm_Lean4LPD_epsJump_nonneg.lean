-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_nonneg
-- name    : Lean4LPD.epsJump_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:10.1228+00:00
-- url     : https://prove2.me/theorems/72b29291-3322-41f3-88a0-fa1f5b658153
-- title:
--   Lean4 LPD: eps Jump nonneg
-- statement:
--   The Lean4 LPD construction uses the eps Jump nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L94-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L94-L99

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.epsJump_nonneg {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (j nu : ℕ)
    (h : 1 ≤ nu + j) : 0 ≤ epsJump kh1 c a j nu := by sorry
