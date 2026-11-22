-- Prove2me | Theorems.Thm_Nock_evalGPaper_le_evalPaperMod
-- name    : Nock.evalGPaper_le_evalPaperMod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:48.378658+00:00
-- url     : https://prove2.me/theorems/4c2a6a72-8564-4f32-95c3-cc0537580a2a
-- title:
--   Nock: eval GPaper le eval Paper Mod
-- statement:
--   **`evalGPaper q` refines `evalPaperMod q`.**  A successful guarded run is a strict-paper
--       modular run with the same value: the guard rules out the wrap that is the only difference.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L185-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L185-L190

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalGPaper_le_evalPaperMod {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalPaperMod q n s form = some r := by sorry
