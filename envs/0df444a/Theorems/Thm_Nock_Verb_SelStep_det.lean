-- Prove2me | Theorems.Thm_Nock_Verb_SelStep_det
-- name    : Nock.Verb.SelStep.det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:12.939653+00:00
-- url     : https://prove2.me/theorems/908bace2-b317-430f-ac80-68381451c973
-- title:
--   Sel Step: det
-- statement:
--   **Determinism from strictness.**  If `lt` is a strict total order, a redex-selection
--       step is deterministic: `hs.total` forces the two selected indices to coincide; the rest
--       is functionality of `map`/`reduce`/`replaceAt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L582-L597
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L582-L597

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.SelStep.det {lt : Nat → Nat → Prop} (hs : StrictSelect lt) {a b b' : Verb}
    (h : SelStep lt a b) (h' : SelStep lt a b') : b = b' := by sorry
