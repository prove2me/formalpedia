-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_termSign_ne_zero
-- name    : LeanPool.ListEdgeColoringComplete.termSign_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:42:48.582281+00:00
-- url     : https://prove2.me/theorems/81dd97f9-d6d2-4229-986b-4771dc016246
-- title:
--   List Edge Coloring Complete: term Sign ne zero
-- statement:
--   The List Edge Coloring Complete construction uses the term Sign ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L207-L211
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L207-L211

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
omit [DecidableEq V]

theorem LeanPool.ListEdgeColoringComplete.termSign_ne_zero [Fintype V] (P : V → Equiv.Perm (Fin n)) : termSign P ≠ 0 := by sorry
