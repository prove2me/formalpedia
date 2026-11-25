-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_eq_inl
-- name    : LeanPool.ListEdgeColoringComplete.starMember_eq_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:37:30.167997+00:00
-- url     : https://prove2.me/theorems/5ef3dc48-6eec-41d0-8e82-d7ac195465a0
-- title:
--   List Edge Coloring Complete: star Member eq inl
-- statement:
--   The members of the star at `u` equal to a given actual edge `s(a, b)`.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L76-L95
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L76-L95

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

theorem LeanPool.ListEdgeColoringComplete.starMember_eq_inl (f : V ≃ Fin n) (u a b : V) (k : Fin n)
    (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    starMember f u k = Sum.inl ⟨s(a, b), hab⟩ ↔
      (u = a ∧ k = f b) ∨ (u = b ∧ k = f a) := by sorry
