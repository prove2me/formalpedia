-- Prove2me | Theorems.Thm_Nock_NPR_leafF_cell
-- name    : Nock.NPR.leafF_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:10.393708+00:00
-- url     : https://prove2.me/theorems/3be54278-5063-460b-ac67-70d576870527
-- title:
--   NPR: leaf F cell
-- statement:
--   Leaf array concatenates under `cell` (DFS order), main.tex:1218.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L232-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L232-L234

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

theorem Nock.NPR.leafF_cell (l r : Noun) :
    leafF (K := K) (Noun.cell l r) = leafF l ++ leafF r := by sorry
