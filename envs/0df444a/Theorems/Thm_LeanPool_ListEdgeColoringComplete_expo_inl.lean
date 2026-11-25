-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_inl
-- name    : LeanPool.ListEdgeColoringComplete.expo_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:36:48.916713+00:00
-- url     : https://prove2.me/theorems/796b5a5c-4eeb-4df7-b239-231daf12a26a
-- title:
--   List Edge Coloring Complete: expo inl
-- statement:
--   The List Edge Coloring Complete construction uses the expo inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L154-L166
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean#L154-L166

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

theorem LeanPool.ListEdgeColoringComplete.expo_inl [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) (a b : V)
    (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    expo f P (Sum.inl ⟨s(a, b), hab⟩) = P a (f b) + P b (f a) := by sorry
