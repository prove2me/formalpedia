-- Prove2me | Theorems.Thm_GJKKL_card_loss_le
-- name    : GJKKL.card_loss_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:18.176054+00:00
-- url     : https://prove2.me/theorems/17123db9-c8d5-409e-ab85-71f79d32d4fa
-- title:
--   GJKKL: card loss le
-- statement:
--   A single choice `a ∌ v` removes at most `|a| · c` edges through `v`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L157-L168
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L157-L168

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.card_loss_le (H : Finset (Finset V)) (h : List (Finset V)) {v : V} {a : Finset V}
    (hva : v ∉ a) {c : ℕ} (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card ≤ a.card * c := by sorry
