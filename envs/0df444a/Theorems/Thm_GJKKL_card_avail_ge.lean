-- Prove2me | Theorems.Thm_GJKKL_card_avail_ge
-- name    : GJKKL.card_avail_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:25.137815+00:00
-- url     : https://prove2.me/theorems/fba56e1f-62e0-42f2-9867-8c228bacb53c
-- title:
--   GJKKL: card avail ge
-- statement:
--   **Number of available edges.** If every chosen edge has at most `k` vertices and every
--   vertex has degree at most `D`, then at least `|H| - |h| k D` edges remain available.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L101-L118
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L101-L118

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

theorem GJKKL.card_avail_ge (H : Finset (Finset V)) {k D : ℕ} (hdeg : ∀ v, degree H v ≤ D) :
    ∀ h : List (Finset V), (∀ f ∈ h, f.card ≤ k) →
      H.card ≤ (avail H h).card + h.length * (k * D)
  := by sorry
