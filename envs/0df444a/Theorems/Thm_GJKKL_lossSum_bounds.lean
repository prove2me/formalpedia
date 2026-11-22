-- Prove2me | Theorems.Thm_GJKKL_lossSum_bounds
-- name    : GJKKL.lossSum_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:25.867655+00:00
-- url     : https://prove2.me/theorems/b1a1c4f9-00a6-4273-aff5-e29a85bb2d4c
-- title:
--   GJKKL: loss Sum bounds
-- statement:
--   Two-sided bounds for `lossSum` in terms of the remaining degrees of the other vertices of
--   the edges through `v`. Here every edge has `k` vertices and all codegrees are at most `c`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L135-L154
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L135-L154

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.lossSum_bounds (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    (h : List (Finset V)) (v : V) {c : ℕ} (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    lossSum H h v ≤ ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, dv H h u ∧
      ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, dv H h u ≤
        lossSum H h v + (Dv H h v).card * ((k - 1) * c + (k - 1) * (k - 2) * c) := by sorry
