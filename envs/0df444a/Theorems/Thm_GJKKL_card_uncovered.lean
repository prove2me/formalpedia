-- Prove2me | Theorems.Thm_GJKKL_card_uncovered
-- name    : GJKKL.card_uncovered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:02.07481+00:00
-- url     : https://prove2.me/theorems/8bed9fcf-0adf-420b-9b84-32ee6051793e
-- title:
--   GJKKL: card uncovered
-- statement:
--   After a greedy sequence of length `t` in a `k`-graph, `n - k t` vertices are uncovered.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L113-L118
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L113-L118

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.card_uncovered {H : Finset (Finset V)} {k : ℕ} (hk : IsUniform H k)
    {h : List (Finset V)} (hh : IsGreedySeq H h) :
    (uncovered h).card + k * h.length = Fintype.card V := by sorry
