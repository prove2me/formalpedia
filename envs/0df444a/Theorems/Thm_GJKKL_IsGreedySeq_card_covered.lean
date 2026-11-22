-- Prove2me | Theorems.Thm_GJKKL_IsGreedySeq_card_covered
-- name    : GJKKL.IsGreedySeq.card_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:34.107384+00:00
-- url     : https://prove2.me/theorems/fd0e5b17-1c1f-4483-8cce-6a4a314805dd
-- title:
--   Is Greedy Seq: card covered
-- statement:
--   The number of vertices covered by a greedy sequence of `k`-sets is `k` times its
--   length.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L240-L249
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L240-L249

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.IsGreedySeq.card_covered {H : Finset (Finset V)} {k : ℕ} (hk : IsUniform H k) :
    ∀ {h : List (Finset V)}, IsGreedySeq H h → (covered h).card = k * h.length
  := by sorry
