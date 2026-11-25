-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_canonicalPerm_inr_lt
-- name    : LeanPool.ListEdgeColoringComplete.expo_canonicalPerm_inr_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:47:36.75084+00:00
-- url     : https://prove2.me/theorems/775808e3-adc2-578b-abdb-ffdf50bff7b2
-- title:
--   List Edge Coloring Complete: expo canonical Perm inr lt
-- statement:
--   The certificate exponent of an artificial vertex is its blocked value, below `n`.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean#L72-L75
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean#L72-L75

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}

theorem LeanPool.ListEdgeColoringComplete.expo_canonicalPerm_inr_lt [Fintype V] (f : V ≃ Fin n) (u : V) :
    expo f (canonicalPerm f) (Sum.inr u) < n := by sorry
