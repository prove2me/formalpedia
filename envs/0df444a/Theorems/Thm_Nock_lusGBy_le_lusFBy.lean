-- Prove2me | Theorems.Thm_Nock_lusGBy_le_lusFBy
-- name    : Nock.lusGBy_le_lusFBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:16.652798+00:00
-- url     : https://prove2.me/theorems/caf1dbd7-bafe-4598-ac9b-60729355c733
-- title:
--   Nock: lus GBy le lus FBy
-- statement:
--   A successful guarded increment is the paper's modular increment (`main.tex:1531–1534`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L151-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L151-L159

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.lusGBy_le_lusFBy {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : FieldEmbedding.lusFBy q x = some m := by sorry
