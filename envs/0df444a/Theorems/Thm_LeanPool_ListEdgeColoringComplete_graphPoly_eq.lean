-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_graphPoly_eq
-- name    : LeanPool.ListEdgeColoringComplete.graphPoly_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:36:17.651903+00:00
-- url     : https://prove2.me/theorems/97f85df3-2393-59ee-86cb-dd4580801208
-- title:
--   List Edge Coloring Complete: graph Poly eq
-- statement:
--   The List Edge Coloring Complete construction uses the graph Poly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L133-L142
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L133-L142

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

theorem LeanPool.ListEdgeColoringComplete.graphPoly_eq [Fintype V] (f : V ≃ Fin n) :
    graphPoly f = ∑ P : V → Equiv.Perm (Fin n), monomial (expo f P) (termSign P) := by sorry
