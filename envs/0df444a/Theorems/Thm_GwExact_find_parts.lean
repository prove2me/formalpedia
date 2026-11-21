-- Prove2me | Theorems.Thm_GwExact_find_parts
-- name    : GwExact.find_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:46.887684+00:00
-- url     : https://prove2.me/theorems/cba52f5e-51dd-4851-998a-e6e67569330c
-- title:
--   Gw Exact: find parts
-- statement:
--   `find` in terms of the parts of a trie (also for a leaf).
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L137-L141
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L137-L141

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.find_parts (t : Trie) (k : Nat) :
    t.find k = if k = 0 then t.val else if k % 2 = 1 then t.left.find (k / 2) else t.right.find (k / 2 - 1) := by sorry
