-- Prove2me | Theorems.Thm_GJKKL_frozen_cons_of_mem
-- name    : GJKKL.frozen_cons_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:44.30206+00:00
-- url     : https://prove2.me/theorems/a286d28a-cb96-4ab0-8b6c-65ed6bb6e9e5
-- title:
--   GJKKL: frozen cons of mem
-- statement:
--   The GJKKL construction uses the frozen cons of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L52-L55
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L52-L55

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

theorem GJKKL.frozen_cons_of_mem (H : Finset (Finset V)) (F : ℕ → ℝ → ℝ) {v : V} {a : Finset V}
    (h : List (Finset V)) (hva : v ∈ a) : frozen H F v (a :: h) = frozen H F v h := by sorry
