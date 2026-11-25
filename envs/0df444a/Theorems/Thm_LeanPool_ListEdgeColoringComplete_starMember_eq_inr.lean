-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_eq_inr
-- name    : LeanPool.ListEdgeColoringComplete.starMember_eq_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:36:54.645735+00:00
-- url     : https://prove2.me/theorems/21d47d62-1116-5cf4-ae72-ee95716152e4
-- title:
--   List Edge Coloring Complete: star Member eq inr
-- statement:
--   The members of the star at `u` equal to a given artificial vertex.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L63-L73
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L63-L73

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}

theorem LeanPool.ListEdgeColoringComplete.starMember_eq_inr (f : V ≃ Fin n) (u w : V) (k : Fin n) :
    starMember f u k = Sum.inr w ↔ u = w ∧ k = f u := by sorry
