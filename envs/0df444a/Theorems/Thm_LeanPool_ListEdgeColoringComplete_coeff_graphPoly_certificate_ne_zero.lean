-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_coeff_graphPoly_certificate_ne_zero
-- name    : LeanPool.ListEdgeColoringComplete.coeff_graphPoly_certificate_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:36:45.06447+00:00
-- url     : https://prove2.me/theorems/b013222b-e20a-56d0-993c-e753f287503a
-- title:
--   List Edge Coloring Complete: coeff graph Poly certificate ne zero
-- statement:
--   The List Edge Coloring Complete construction uses the coeff graph Poly certificate ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L224-L227
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L224-L227

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

theorem LeanPool.ListEdgeColoringComplete.coeff_graphPoly_certificate_ne_zero [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).coeff (expo f (canonicalPerm f)) ≠ 0 := by sorry
