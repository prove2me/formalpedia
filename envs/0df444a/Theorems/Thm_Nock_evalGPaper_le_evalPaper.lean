-- Prove2me | Theorems.Thm_Nock_evalGPaper_le_evalPaper
-- name    : Nock.evalGPaper_le_evalPaper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:49.652216+00:00
-- url     : https://prove2.me/theorems/ed22fed5-99fb-4a58-8ba1-747ee034b9db
-- title:
--   Nock: eval GPaper le eval Paper
-- statement:
--   **`evalGPaper q` refines `evalPaper`.**  Under the guard the fragment's modular-range OP₄ and
--       the unbounded Nat OP₄ coincide, so a successful guarded run is a `evalPaper` run with the same
--       value — the entry point into the unconditional `runProgram ↔ evalPaper` adequacy.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L176-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L176-L181

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalGPaper_le_evalPaper {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalPaper n s form = some r := by sorry
