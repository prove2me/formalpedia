-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_eq_canonicalPerm_of_expo_eq
-- name    : LeanPool.ListEdgeColoringComplete.eq_canonicalPerm_of_expo_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:41:52.358425+00:00
-- url     : https://prove2.me/theorems/cf400e6d-08e0-5731-a887-2aeede761e90
-- title:
--   List Edge Coloring Complete: eq canonical Perm of expo eq
-- statement:
--   Only the canonical family of permutations produces the certificate monomial. This is
--   where the uniqueness of the certificate enters.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L185-L204
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L185-L204

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

theorem LeanPool.ListEdgeColoringComplete.eq_canonicalPerm_of_expo_eq [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n))
    (h : expo f P = expo f (canonicalPerm f)) : P = canonicalPerm f := by sorry
