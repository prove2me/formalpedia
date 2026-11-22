-- Prove2me | Theorems.Thm_Nock_Noun_size_add_one
-- name    : Nock.Noun.size_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:09.32566+00:00
-- url     : https://prove2.me/theorems/bfbd5ea6-033a-4b16-9dc9-bf35e800de24
-- title:
--   Noun: size add one
-- statement:
--   The Noun construction uses the size add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L60-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L60-L63

module
public import Definitions.Def_LeanPool_PureNock_Tree
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.size_add_one (n : Noun) : n.size + 1 = 2 * n.leaves := by sorry
