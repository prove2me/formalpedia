-- Prove2me | Theorems.Thm_Nock_run_length
-- name    : Nock.run_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:47.521047+00:00
-- url     : https://prove2.me/theorems/02ce8b5c-015b-4ceb-807d-38aeb433dd8b
-- title:
--   Nock: run length
-- statement:
--   An accepting run consumes a transcript of length exactly `msize m` (the total node count
--       of the initial multiset).  This is the necessity half of `Thm:Noun_Validation`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L168-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L168-L187

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.run_length : ∀ {m : Multiset Noun} {T : Transcript},
    runMset m T = some 0 → T.length = msize m := by sorry
