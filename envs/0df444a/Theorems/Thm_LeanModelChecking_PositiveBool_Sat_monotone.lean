-- Prove2me | Theorems.Thm_LeanModelChecking_PositiveBool_Sat_monotone
-- name    : LeanModelChecking.PositiveBool.Sat.monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:34.577455+00:00
-- url     : https://prove2.me/theorems/b102a499-b6c8-4052-9156-6a522a6c6bb2
-- title:
--   Sat: monotone
-- statement:
--   The Sat construction uses the monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABW.lean#L41-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABW.lean#L41-L43

module
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking

theorem LeanModelChecking.PositiveBool.Sat.monotone {Q} {f : PositiveBool Q} {A B : Set Q} :
    A ⊆ B → PositiveBool.Sat A f → PositiveBool.Sat B f := by sorry
