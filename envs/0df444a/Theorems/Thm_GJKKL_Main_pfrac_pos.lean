-- Prove2me | Theorems.Thm_GJKKL_Main_pfrac_pos
-- name    : GJKKL.Main.pfrac_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:20:14.672552+00:00
-- url     : https://prove2.me/theorems/05f143aa-0afe-4b9d-8dc5-626dea78681a
-- title:
--   Main: pfrac pos
-- statement:
--   The Main construction uses the pfrac pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L296-L298
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L296-L298

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
variable {a μ x y : ℝ}

theorem GJKKL.Main.pfrac_pos {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) {m t : ℕ} (hm : (m : ℝ) ≤ (1 - μ) * a)
    (ht : t ≤ m) : 0 < pfrac a t := by sorry
