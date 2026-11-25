-- Prove2me | Theorems.Thm_MatrixTree_card_ne_add_one
-- name    : MatrixTree.card_ne_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:00:53.045185+00:00
-- url     : https://prove2.me/theorems/ef6da396-039f-4837-970b-edd4417ce38a
-- title:
--   Matrix Tree: card ne add one
-- statement:
--   The Matrix Tree construction uses the card ne add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L320-L326
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L320-L326

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem MatrixTree.card_ne_add_one [Finite V] (v : V) : Nat.card {u // u ≠ v} + 1 = Nat.card V := by sorry
