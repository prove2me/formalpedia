-- Prove2me | Theorems.Thm_Nock_NPR_leafF_length
-- name    : Nock.NPR.leafF_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:54.160607+00:00
-- url     : https://prove2.me/theorems/91251b73-6f65-47da-ac0b-133582f390c0
-- title:
--   NPR: leaf F length
-- statement:
--   The NPR construction uses the leaf F length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L181-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L181-L182

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]

theorem Nock.NPR.leafF_length (n : Noun) : (leafF (K := K) n).length = n.leaves := by sorry
