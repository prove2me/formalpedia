-- Prove2me | Theorems.Thm_GJKKL_frozen_cons_of_covered
-- name    : GJKKL.frozen_cons_of_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:49.008022+00:00
-- url     : https://prove2.me/theorems/993d95f2-6160-4d81-bfe5-776d3a53933f
-- title:
--   GJKKL: frozen cons of covered
-- statement:
--   The GJKKL construction uses the frozen cons of covered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L57-L60
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L57-L60

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

theorem GJKKL.frozen_cons_of_covered (H : Finset (Finset V)) (F : ℕ → ℝ → ℝ) {v : V} (a : Finset V)
    {h : List (Finset V)} (hv : v ∈ covered h) : frozen H F v (a :: h) = frozen H F v h := by sorry
