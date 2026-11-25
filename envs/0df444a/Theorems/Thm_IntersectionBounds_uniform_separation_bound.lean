-- Prove2me | Theorems.Thm_IntersectionBounds_uniform_separation_bound
-- name    : IntersectionBounds.uniform_separation_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T12:49:48.889158+00:00
-- url     : https://prove2.me/theorems/a3af3472-d3fb-5467-a534-308d0e53bb2b
-- title:
--   Intersection Bounds: uniform separation bound
-- statement:
--   The Intersection Bounds construction uses the uniform separation bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L22-L32
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L22-L32

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
open Classical

theorem IntersectionBounds.uniform_separation_bound {K : Type v} [Field K] [CharZero K]
    (F : Finset (Finset V)) (L : Finset K) (k : ℕ)
    (huni : Uniform F k) (hs : L.card ≤ k)
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ (Fintype.card V).choose L.card := by sorry
