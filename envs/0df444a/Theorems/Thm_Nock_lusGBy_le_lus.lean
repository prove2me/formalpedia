-- Prove2me | Theorems.Thm_Nock_lusGBy_le_lus
-- name    : Nock.lusGBy_le_lus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:18.426702+00:00
-- url     : https://prove2.me/theorems/79aaaaad-d065-4387-ac7a-d26263f4aa25
-- title:
--   Nock: lus GBy le lus
-- statement:
--   A successful guarded increment is the unbounded increment (`main.tex:1531–1534` vs `Noun.lus`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L140-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L140-L148

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.lusGBy_le_lus {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : Noun.lus x = some m := by sorry
