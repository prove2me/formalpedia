-- Prove2me | Theorems.Thm_Nock_evalFBy_of_evalGPaper
-- name    : Nock.evalFBy_of_evalGPaper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:04.66223+00:00
-- url     : https://prove2.me/theorems/88e8f072-e6ef-4036-b694-0f71e441b672
-- title:
--   Nock: eval FBy of eval GPaper
-- statement:
--   The bridge's field half: a successful guarded fragment run is a full modular run.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L275-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L275-L278

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalFBy_of_evalGPaper {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) :
    FieldEmbedding.evalFBy q fuel s f = some r := by sorry
