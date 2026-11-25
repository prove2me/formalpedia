-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_eval_starPoly
-- name    : LeanPool.ListEdgeColoringComplete.eval_starPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:37:48.428885+00:00
-- url     : https://prove2.me/theorems/b3d93cf7-4642-412b-bbb5-75f43743f13a
-- title:
--   List Edge Coloring Complete: eval star Poly
-- statement:
--   The List Edge Coloring Complete construction uses the eval star Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L115-L122
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L115-L122

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

theorem LeanPool.ListEdgeColoringComplete.eval_starPoly (f : V ≃ Fin n) (u : V) (x : StarVar V → ℚ) :
    eval x (starPoly f u) =
      (Matrix.vandermonde (fun k => x (starMember f u k))).det := by sorry
