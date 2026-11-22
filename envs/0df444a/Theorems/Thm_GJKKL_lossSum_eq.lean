-- Prove2me | Theorems.Thm_GJKKL_lossSum_eq
-- name    : GJKKL.lossSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:04.76425+00:00
-- url     : https://prove2.me/theorems/4e886df3-22cb-45aa-9a95-bf2eaed29d40
-- title:
--   GJKKL: loss Sum eq
-- statement:
--   The GJKKL construction uses the loss Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L58-L62
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L58-L62

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.lossSum_eq (H : Finset (Finset V)) (h : List (Finset V)) (v : V) :
    lossSum H h v = ∑ f ∈ Dv H h v, (hitters H h v f).card := by sorry
