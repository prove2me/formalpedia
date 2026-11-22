-- Prove2me | Theorems.Thm_Nock_runProgram_of_evalGPaper
-- name    : Nock.runProgram_of_evalGPaper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:02.067+00:00
-- url     : https://prove2.me/theorems/23e210a4-5f76-415e-80d5-2428c5388128
-- title:
--   Nock: run Program of eval GPaper
-- statement:
--   The bridge's small-step half in the form the machine consumes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L270-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L270-L272

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.runProgram_of_evalGPaper {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) : ∃ n, Verb.runProgram n s f = some r := by sorry
