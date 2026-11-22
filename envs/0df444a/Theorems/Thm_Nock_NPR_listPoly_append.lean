-- Prove2me | Theorems.Thm_Nock_NPR_listPoly_append
-- name    : Nock.NPR.listPoly_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:27.40265+00:00
-- url     : https://prove2.me/theorems/9a0a29c3-7b9a-4678-a139-590e9a856e22
-- title:
--   NPR: list Poly append
-- statement:
--   **`listPoly (a ++ b) = listPoly a + X^{|a|} · listPoly b`** — the paper's stated
--       concatenation rule (main.tex:1218 discussion): a coefficient list `a ++ b` gives the
--       polynomial of `a` plus the polynomial of `b` shifted up by `|a|` places.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L160-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L160-L166

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

theorem Nock.NPR.listPoly_append (a b : List K) :
    listPoly (a ++ b) = listPoly a + X ^ a.length * listPoly b := by sorry
