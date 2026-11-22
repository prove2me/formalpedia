-- Prove2me | Theorems.Thm_Nock_evalPaperMod_mono
-- name    : Nock.evalPaperMod_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:13.065803+00:00
-- url     : https://prove2.me/theorems/fd627241-152d-426d-ad7e-57c06e2ffc1c
-- title:
--   Nock: eval Paper Mod mono
-- statement:
--   **Fuel monotonicity** for `evalPaperMod`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L129-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L129-L133

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaperMod_mono {q n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalPaperMod q n s form = some r) : evalPaperMod q m s form = some r := by sorry
