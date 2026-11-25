-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_inr
-- name    : LeanPool.ListEdgeColoringComplete.expo_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:42:17.28573+00:00
-- url     : https://prove2.me/theorems/633b2273-bf8f-4719-8b70-04936d2dc1ee
-- title:
--   List Edge Coloring Complete: expo inr
-- statement:
--   The List Edge Coloring Complete construction uses the expo inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L144-L152
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L144-L152

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

theorem LeanPool.ListEdgeColoringComplete.expo_inr [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) (u : V) :
    expo f P (Sum.inr u) = P u (f u) := by sorry
