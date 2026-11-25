-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_totalDegree_graphPoly
-- name    : LeanPool.ListEdgeColoringComplete.totalDegree_graphPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:47:15.795658+00:00
-- url     : https://prove2.me/theorems/831f7488-8185-45cc-b9ee-365fd6f809ab
-- title:
--   List Edge Coloring Complete: total Degree graph Poly
-- statement:
--   The total degree of the polynomial equals the degree of the certificate monomial.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L230-L240
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L230-L240

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

theorem LeanPool.ListEdgeColoringComplete.totalDegree_graphPoly [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).totalDegree = (expo f (canonicalPerm f)).degree := by sorry
