-- Prove2me | Theorems.Thm_Nock_evalPaperMod_succ
-- name    : Nock.evalPaperMod_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:06.415579+00:00
-- url     : https://prove2.me/theorems/a2af1aa7-f2e7-47c8-9912-62b96b0b90cf
-- title:
--   Nock: eval Paper Mod succ
-- statement:
--   **Fuel monotonicity (single step)** for `evalPaperMod`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L114-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L114-L126

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaperMod_succ {q n : Nat} {s form r : Noun}
    (h : evalPaperMod q n s form = some r) : evalPaperMod q (n + 1) s form = some r := by sorry
