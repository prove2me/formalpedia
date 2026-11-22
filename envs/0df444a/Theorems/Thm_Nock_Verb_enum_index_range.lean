-- Prove2me | Theorems.Thm_Nock_Verb_enum_index_range
-- name    : Nock.Verb.enum_index_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:52.43852+00:00
-- url     : https://prove2.me/theorems/e4b4ac97-8e23-4d7e-9682-e47f99bfb275
-- title:
--   Verb: enum index range
-- statement:
--   Every internal-node index produced by `enum v c` lies in the half-open counter range
--       `[c, (enum v c).1)`.  Distinct nodes therefore receive distinct indices: the DFS
--       `map` enforces a *strict* ordering on subtrees (main.tex:1107).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L346-L360
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L346-L360

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.enum_index_range (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, c ≤ p.1 ∧ p.1 < (enum v c).1 := by sorry
