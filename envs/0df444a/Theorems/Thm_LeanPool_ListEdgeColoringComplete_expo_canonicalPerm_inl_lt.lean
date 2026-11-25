-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_canonicalPerm_inl_lt
-- name    : LeanPool.ListEdgeColoringComplete.expo_canonicalPerm_inl_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:47:33.583935+00:00
-- url     : https://prove2.me/theorems/15e86a00-bc24-508d-8088-4357b7e062db
-- title:
--   List Edge Coloring Complete: expo canonical Perm inl lt
-- statement:
--   The certificate exponent of an actual edge is its target degree, at most `n - 1`.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean#L55-L69
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean#L55-L69

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

theorem LeanPool.ListEdgeColoringComplete.expo_canonicalPerm_inl_lt [Fintype V] (f : V ≃ Fin n)
    (e : (⊤ : SimpleGraph V).edgeSet) : expo f (canonicalPerm f) (Sum.inl e) < n := by sorry
