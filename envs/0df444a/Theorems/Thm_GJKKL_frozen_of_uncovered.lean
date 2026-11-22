-- Prove2me | Theorems.Thm_GJKKL_frozen_of_uncovered
-- name    : GJKKL.frozen_of_uncovered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:50.402195+00:00
-- url     : https://prove2.me/theorems/4c494efd-8cb7-443e-a1ce-5cb7e2cec703
-- title:
--   GJKKL: frozen of uncovered
-- statement:
--   The GJKKL construction uses the frozen of uncovered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L47-L50
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L47-L50

module
public import Definitions.Def_GJKKL_Greedy_Drift
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Trajectory_Frozen
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.frozen_of_uncovered (H : Finset (Finset V)) (F : ℕ → ℝ → ℝ) (v : V) :
    ∀ {h : List (Finset V)}, v ∉ covered h → frozen H F v h = F h.length (dv H h v)
  := by sorry
