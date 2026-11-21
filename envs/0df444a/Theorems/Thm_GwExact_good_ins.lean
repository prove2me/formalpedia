-- Prove2me | Theorems.Thm_GwExact_good_ins
-- name    : GwExact.good_ins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:01.994291+00:00
-- url     : https://prove2.me/theorems/5daed3f2-bf7e-4f75-aa1d-460066d94909
-- title:
--   Gw Exact: good ins
-- statement:
--   The Gw Exact construction uses the good ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L183-L188
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L183-L188

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.good_ins {σ : Nat → Bool} {db : Trie} (hdb : Good σ db) (f k : Nat) {c : Cls}
    (hc : c.Holds σ) : Good σ (Trie.ins f db k c) := by sorry
