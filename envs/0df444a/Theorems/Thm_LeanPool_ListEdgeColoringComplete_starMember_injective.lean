-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_injective
-- name    : LeanPool.ListEdgeColoringComplete.starMember_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:48:28.006392+00:00
-- url     : https://prove2.me/theorems/696eea71-2289-4d87-91eb-23764ed1e98f
-- title:
--   List Edge Coloring Complete: star Member injective
-- statement:
--   The List Edge Coloring Complete construction uses the star Member injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L50-L60
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L50-L60

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

theorem LeanPool.ListEdgeColoringComplete.starMember_injective (f : V ≃ Fin n) (u : V) :
    Function.Injective (starMember f u) := by sorry
