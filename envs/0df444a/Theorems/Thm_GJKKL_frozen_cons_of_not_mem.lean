-- Prove2me | Theorems.Thm_GJKKL_frozen_cons_of_not_mem
-- name    : GJKKL.frozen_cons_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:52.884317+00:00
-- url     : https://prove2.me/theorems/56ae0509-4588-4db4-9ad7-3e72d30bfa71
-- title:
--   GJKKL: frozen cons of not mem
-- statement:
--   A choice that does not cover `v` decreases `d_v` by the number of edges of `D_v` it
--   meets.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L64-L74
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean#L64-L74

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

theorem GJKKL.frozen_cons_of_not_mem (H : Finset (Finset V)) (F : ℕ → ℝ → ℝ) {v : V} {a : Finset V}
    {h : List (Finset V)} (hv : v ∉ covered h) (hva : v ∉ a) :
    frozen H F v (a :: h) =
      F (h.length + 1) ((dv H h v : ℝ) - ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card) := by sorry
