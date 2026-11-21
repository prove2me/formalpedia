-- Prove2me | Theorems.Thm_GwExact_ins_succ
-- name    : GwExact.ins_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:47.004045+00:00
-- url     : https://prove2.me/theorems/3b009479-b70a-49c8-b7aa-67eacb98bd93
-- title:
--   Gw Exact: ins succ
-- statement:
--   The Gw Exact construction uses the ins succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L143-L148
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L143-L148

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.ins_succ (f : Nat) (t : Trie) (k : Nat) (c : Cls) :
    Trie.ins (f + 1) t k c =
      if k = 0 then .node t.left (some c) t.right
      else if k % 2 = 1 then .node (Trie.ins f t.left (k / 2) c) t.val t.right
      else .node t.left t.val (Trie.ins f t.right (k / 2 - 1) c) := by sorry
