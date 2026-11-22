-- Prove2me | Theorems.Thm_Nock_evalPaper_mono
-- name    : Nock.evalPaper_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:03.096516+00:00
-- url     : https://prove2.me/theorems/9c19e582-280e-4cc3-b3ea-1d7f78f0de6a
-- title:
--   Nock: eval Paper mono
-- statement:
--   **Fuel monotonicity** for `evalPaper`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean#L106-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean#L106-L110

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_PaperReference
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaper_mono {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalPaper n s form = some r) : evalPaper m s form = some r := by sorry
