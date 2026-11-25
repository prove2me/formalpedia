-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_degree_expo
-- name    : LeanPool.ListEdgeColoringComplete.degree_expo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:41:49.757222+00:00
-- url     : https://prove2.me/theorems/63bdffc5-f8e1-5078-80aa-23e85d7d4342
-- title:
--   List Edge Coloring Complete: degree expo
-- statement:
--   The List Edge Coloring Complete construction uses the degree expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L168-L172
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L168-L172

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

theorem LeanPool.ListEdgeColoringComplete.degree_expo [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) :
    (expo f P).degree = Fintype.card V * ∑ k : Fin n, (k : ℕ) := by sorry
