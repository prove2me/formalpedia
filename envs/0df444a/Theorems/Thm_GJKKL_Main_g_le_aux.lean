-- Prove2me | Theorems.Thm_GJKKL_Main_g_le_aux
-- name    : GJKKL.Main.g_le_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:26.298358+00:00
-- url     : https://prove2.me/theorems/4919bea0-1a52-48fa-ab6d-971eeb749c78
-- title:
--   Main: g le aux
-- statement:
--   Upper bound for the one-step decrease of `d x^{j+1}`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L301-L314
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L301-L314

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

theorem GJKKL.Main.g_le_aux {x y a d : ℝ} (j : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) (hx : 0 < x) (ha : 0 < a)
    (hd : 0 ≤ d) (hxy' : x - y = 1 / a) :
    d * x ^ (j + 1) - d * y ^ (j + 1) ≤ ((j : ℝ) + 1) * (d * x ^ (j + 1)) / (a * x) := by sorry
