-- Prove2me | Theorems.Thm_GJKKL_card_hitters_le
-- name    : GJKKL.card_hitters_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:11.761783+00:00
-- url     : https://prove2.me/theorems/f45b2cf5-d993-4800-a68c-03d60244aa7d
-- title:
--   GJKKL: card hitters le
-- statement:
--   Upper bound for the hitters of `f`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L82-L87
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L82-L87

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.card_hitters_le (H : Finset (Finset V)) (h : List (Finset V)) (v : V) (f : Finset V) :
    (hitters H h v f).card ≤ ∑ u ∈ f.erase v, dv H h u := by sorry
