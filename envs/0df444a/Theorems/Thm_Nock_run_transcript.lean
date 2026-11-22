-- Prove2me | Theorems.Thm_Nock_run_transcript
-- name    : Nock.run_transcript
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:50.006856+00:00
-- url     : https://prove2.me/theorems/556f78b5-368c-48b5-86b3-d2cfbd098641
-- title:
--   Nock: run transcript
-- statement:
--   Processing `transcript n` off the front of a multiset containing `n` validates `n` and
--       removes exactly `n`, leaving the rest of the walk untouched.  (Order-independence of the
--       walk, main.tex:1266: we use preorder.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L207-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L207-L225

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

theorem Nock.run_transcript : ∀ (n : Noun) (m : Multiset Noun) (rest : Transcript),
    runMset (n ::ₘ m) (transcript n ++ rest) = runMset m rest := by sorry
