-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalPerm_apply
-- name    : LeanPool.ListEdgeColoringComplete.canonicalPerm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:36:43.364707+00:00
-- url     : https://prove2.me/theorems/06e4628f-f73c-4b36-85f8-22f358305642
-- title:
--   List Edge Coloring Complete: canonical Perm apply
-- statement:
--   The List Edge Coloring Complete construction uses the canonical Perm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L180-L181
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L180-L181

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

theorem LeanPool.ListEdgeColoringComplete.canonicalPerm_apply (f : V ≃ Fin n) (u : V) (k : Fin n) :
    canonicalPerm f u k = canonicalRow (f u) k := by sorry
