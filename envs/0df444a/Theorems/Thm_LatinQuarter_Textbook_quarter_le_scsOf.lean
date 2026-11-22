-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_quarter_le_scsOf
-- name    : LatinQuarter.Textbook.quarter_le_scsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:30.156416+00:00
-- url     : https://prove2.me/theorems/870059ac-acbd-4bf6-bddd-ade452e29a20
-- title:
--   Textbook: quarter le scs Of
-- statement:
--   The Textbook construction uses the quarter le scs Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L191-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L191-L197

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.quarter_le_scsOf {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : Latin L) :
    n * n / 4 ≤ scsOf L := by sorry
