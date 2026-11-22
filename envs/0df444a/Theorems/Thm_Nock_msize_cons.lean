-- Prove2me | Theorems.Thm_Nock_msize_cons
-- name    : Nock.msize_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:34.603185+00:00
-- url     : https://prove2.me/theorems/091e5d1e-74db-42d5-9edd-cefe4847dc46
-- title:
--   Nock: msize cons
-- statement:
--   The Nock construction uses the msize cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L122-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L122-L124

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

theorem Nock.msize_cons (a : Noun) (m : Multiset Noun) :
    msize (a ::ₘ m) = a.size + msize m := by sorry
