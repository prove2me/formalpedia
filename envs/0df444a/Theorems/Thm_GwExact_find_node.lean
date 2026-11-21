-- Prove2me | Theorems.Thm_GwExact_find_node
-- name    : GwExact.find_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:45.264669+00:00
-- url     : https://prove2.me/theorems/02e60a9f-72b8-4b75-b805-96909ad456c6
-- title:
--   Gw Exact: find node
-- statement:
--   The Gw Exact construction uses the find node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L131-L134
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L131-L134

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.find_node (l r : Trie) (v : Option Cls) (k : Nat) :
    (Trie.node l v r).find k =
      if k = 0 then v else if k % 2 = 1 then l.find (k / 2) else r.find (k / 2 - 1) := by sorry
