-- Prove2me | Theorems.Thm_GJKKL_sum_dv
-- name    : GJKKL.sum_dv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:50.891148+00:00
-- url     : https://prove2.me/theorems/2068294e-cf93-40e6-89b2-b89df467e036
-- title:
--   GJKKL: sum dv
-- statement:
--   For a `k`-graph: `Σ_v d_v(h) = k · |H(h)|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L94-L97
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L94-L97

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.sum_dv (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k) (h : List (Finset V)) :
    ∑ v, dv H h v = k * (avail H h).card := by sorry
