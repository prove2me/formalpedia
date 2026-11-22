-- Prove2me | Theorems.Thm_GJKKL_sum_uncovered_dv
-- name    : GJKKL.sum_uncovered_dv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:57.473144+00:00
-- url     : https://prove2.me/theorems/ebb24dd3-498b-476f-8c53-627010847c7e
-- title:
--   GJKKL: sum uncovered dv
-- statement:
--   The sum of the remaining degrees over the uncovered vertices is `k · |H(h)|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L106-L110
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L106-L110

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.sum_uncovered_dv (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    (h : List (Finset V)) :
    ∑ v ∈ uncovered h, dv H h v = k * (avail H h).card := by sorry
