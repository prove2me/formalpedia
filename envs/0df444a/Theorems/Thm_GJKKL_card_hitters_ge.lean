-- Prove2me | Theorems.Thm_GJKKL_card_hitters_ge
-- name    : GJKKL.card_hitters_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:20.469474+00:00
-- url     : https://prove2.me/theorems/691e9bd1-4062-41a5-b291-e4e68bb3cb49
-- title:
--   GJKKL: card hitters ge
-- statement:
--   Lower bound for the hitters of `f`, with codegree errors.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L90-L131
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L90-L131

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.card_hitters_ge (H : Finset (Finset V)) (h : List (Finset V)) (v : V) (f : Finset V)
    {c : ℕ} (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    ∑ u ∈ f.erase v, dv H h u ≤
      (hitters H h v f).card + (f.erase v).card * c + (f.erase v).card * ((f.erase v).card - 1) * c := by sorry
