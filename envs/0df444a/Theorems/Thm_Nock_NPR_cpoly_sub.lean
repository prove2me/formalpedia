-- Prove2me | Theorems.Thm_Nock_NPR_cpoly_sub
-- name    : Nock.NPR.cpoly_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:38.141653+00:00
-- url     : https://prove2.me/theorems/8ca8c8cb-73a6-4e32-a0b1-326d197f4856
-- title:
--   NPR: cpoly sub
-- statement:
--   The NPR construction uses the cpoly sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L68-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L68-L74

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

theorem Nock.NPR.cpoly_sub (f g : ℕ → K) (n : ℕ) :
    cpoly f n - cpoly g n = cpoly (fun i => f i - g i) n := by sorry
