-- Prove2me | Theorems.Thm_GJKKL_mul_degree_le
-- name    : GJKKL.mul_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:25.174855+00:00
-- url     : https://prove2.me/theorems/a375e50a-3e2d-4bb1-a5bf-7f99066375bb
-- title:
--   GJKKL: mul degree le
-- statement:
--   The GJKKL construction uses the mul degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/VertexCount.lean#L41-L55
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/VertexCount.lean#L41-L55

module
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_VertexCount
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.mul_degree_le (H : Finset (Finset V)) {k c : ℕ} (hk : IsUniform H k)
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) (v : V) :
    (k - 1) * degree H v ≤ (Fintype.card V - 1) * c := by sorry
