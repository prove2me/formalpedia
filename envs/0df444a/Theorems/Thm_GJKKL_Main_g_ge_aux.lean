-- Prove2me | Theorems.Thm_GJKKL_Main_g_ge_aux
-- name    : GJKKL.Main.g_ge_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:11.195789+00:00
-- url     : https://prove2.me/theorems/443051a2-92c6-4e4f-9018-5a7e65f121db
-- title:
--   Main: g ge aux
-- statement:
--   Lower bound for the one-step decrease of `d x^{j+1}` (second-order term).
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L317-L349
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L317-L349

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

theorem GJKKL.Main.g_ge_aux {x y a d : ℝ} (j : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) (hx : 0 < x) (ha : 0 < a)
    (hd : 0 ≤ d) (hxy' : x - y = 1 / a) :
    ((j : ℝ) + 1) * (d * x ^ (j + 1)) / (a * x) -
        ((j : ℝ) + 1) * j * (d * x ^ (j + 1)) / (a * x) ^ 2 ≤
      d * x ^ (j + 1) - d * y ^ (j + 1) := by sorry
