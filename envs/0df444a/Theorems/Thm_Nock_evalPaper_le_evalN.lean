-- Prove2me | Theorems.Thm_Nock_evalPaper_le_evalN
-- name    : Nock.evalPaper_le_evalN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:06.6769+00:00
-- url     : https://prove2.me/theorems/6d8526fe-319f-4d03-926f-4dec514ba817
-- title:
--   Nock: eval Paper le eval N
-- statement:
--   **`evalPaper` refines `evalN`.**  Every paper-fragment evaluation is a standard Nock
--       evaluation with the same result: `evalPaper` and `evalN` differ only where `evalN`
--       fires OP₁₁ (which `evalPaper` crashes on).  Proof: functional induction; every clause
--       is identical except OP₁₁, where `evalPaper` returns `none` so the hypothesis is absurd.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean#L124-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean#L124-L129

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_PaperReference
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaper_le_evalN {n : Nat} {s form r : Noun}
    (h : evalPaper n s form = some r) : evalN n s form = some r := by sorry
