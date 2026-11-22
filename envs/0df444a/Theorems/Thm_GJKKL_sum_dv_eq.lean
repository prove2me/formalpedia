-- Prove2me | Theorems.Thm_GJKKL_sum_dv_eq
-- name    : GJKKL.sum_dv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:48.407895+00:00
-- url     : https://prove2.me/theorems/7e68e1dc-1011-4e6d-bd6b-63a029ef6afc
-- title:
--   GJKKL: sum dv eq
-- statement:
--   Double counting: `Σ_v d_v(h) = Σ_{e ∈ H(h)} |e|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L86-L91
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L86-L91

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.sum_dv_eq (H : Finset (Finset V)) (h : List (Finset V)) :
    ∑ v, dv H h v = ∑ e ∈ avail H h, e.card := by sorry
