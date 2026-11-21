-- Prove2me | Theorems.Thm_GwExact_find_ins
-- name    : GwExact.find_ins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:02.515885+00:00
-- url     : https://prove2.me/theorems/534baf4c-cb0b-4e2c-9794-052d14bd6bd8
-- title:
--   Gw Exact: find ins
-- statement:
--   A value found after an insertion is the inserted clause or was found before.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L151-L181
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L151-L181

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.find_ins : ∀ (f : Nat) (t : Trie) (k : Nat) (c : Cls) (k' : Nat) (c' : Cls),
    (Trie.ins f t k c).find k' = some c' → c' = c ∨ t.find k' = some c' := by sorry
