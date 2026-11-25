-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_coeff_graphPoly_certificate
-- name    : LeanPool.ListEdgeColoringComplete.coeff_graphPoly_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:43:05.700647+00:00
-- url     : https://prove2.me/theorems/6e858cb4-ad53-4a81-8a44-ad15990b74ff
-- title:
--   List Edge Coloring Complete: coeff graph Poly certificate
-- statement:
--   **The certificate coefficient is `±1`.**
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L214-L222
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L214-L222

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

theorem LeanPool.ListEdgeColoringComplete.coeff_graphPoly_certificate [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).coeff (expo f (canonicalPerm f)) = termSign (canonicalPerm f) := by sorry
