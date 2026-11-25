-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_starPoly_eval_ne_zero
-- name    : LeanPool.ListEdgeColoringComplete.starPoly_eval_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:41:24.798203+00:00
-- url     : https://prove2.me/theorems/6b97ebbb-585c-491c-8062-983a0490dc26
-- title:
--   List Edge Coloring Complete: star Poly eval ne zero
-- statement:
--   A nonzero value of a star polynomial forces distinct values on the star.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L125-L131
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L125-L131

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

theorem LeanPool.ListEdgeColoringComplete.starPoly_eval_ne_zero (f : V ≃ Fin n) (u : V) (x : StarVar V → ℚ)
    (h : eval x (starPoly f u) ≠ 0) :
    Function.Injective (fun k => x (starMember f u k)) := by sorry
