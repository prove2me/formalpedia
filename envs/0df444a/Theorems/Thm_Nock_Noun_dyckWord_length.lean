-- Prove2me | Theorems.Thm_Nock_Noun_dyckWord_length
-- name    : Nock.Noun.dyckWord_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:23.743463+00:00
-- url     : https://prove2.me/theorems/c6684d0f-2132-446a-a2d4-1a193f4e677a
-- title:
--   Noun: dyck Word length
-- statement:
--   A noun's Dyck word has length `2·leaves − 2 = 2(λ−1)` (main.tex:1164).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L207-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L207-L212

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.dyckWord_length (n : Noun) : n.dyckWord.length + 2 = 2 * n.leaves := by sorry
