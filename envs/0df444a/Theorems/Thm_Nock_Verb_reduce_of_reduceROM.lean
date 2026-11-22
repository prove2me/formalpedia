-- Prove2me | Theorems.Thm_Nock_Verb_reduce_of_reduceROM
-- name    : Nock.Verb.reduce_of_reduceROM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:16.256789+00:00
-- url     : https://prove2.me/theorems/c765229d-e59a-4d10-93fe-17fef0b7f85a
-- title:
--   Verb: reduce of reduce ROM
-- statement:
--   `reduceROM` refines `reduce`: whenever the ROM rewrite succeeds, the full Nock rewrite agrees
--       (they differ only on `OP₁₀`, where `reduceROM` returns `none`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L866-L868
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L866-L868

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.reduce_of_reduceROM {v r : Verb} (h : reduceROM v = some r) : reduce v = some r := by sorry
