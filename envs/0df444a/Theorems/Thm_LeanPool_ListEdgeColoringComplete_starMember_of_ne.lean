-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_of_ne
-- name    : LeanPool.ListEdgeColoringComplete.starMember_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:36:51.961317+00:00
-- url     : https://prove2.me/theorems/c13367ba-30d6-5b0f-8205-4de419bac1ba
-- title:
--   List Edge Coloring Complete: star Member of ne
-- statement:
--   The List Edge Coloring Complete construction uses the star Member of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L46-L48
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L46-L48

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

theorem LeanPool.ListEdgeColoringComplete.starMember_of_ne (f : V ≃ Fin n) {u w : V} (h : w ≠ u) :
    starMember f u (f w) = Sum.inl ⟨s(u, w), by simp [h.symm]⟩ := by sorry
