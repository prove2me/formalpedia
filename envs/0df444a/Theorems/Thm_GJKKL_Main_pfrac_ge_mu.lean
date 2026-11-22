-- Prove2me | Theorems.Thm_GJKKL_Main_pfrac_ge_mu
-- name    : GJKKL.Main.pfrac_ge_mu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:31.262793+00:00
-- url     : https://prove2.me/theorems/da39032d-60ac-47ff-abd0-ec4bfc5ddfd7
-- title:
--   Main: pfrac ge mu
-- statement:
--   The Main construction uses the pfrac ge mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L287-L294
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L287-L294

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

theorem GJKKL.Main.pfrac_ge_mu {a μ : ℝ} (ha : 0 < a) {m t : ℕ} (hm : (m : ℝ) ≤ (1 - μ) * a) (ht : t ≤ m) :
    μ ≤ pfrac a t := by sorry
