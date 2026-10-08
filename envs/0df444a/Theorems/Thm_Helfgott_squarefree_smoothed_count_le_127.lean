-- Prove2me | Theorems.Thm_Helfgott_squarefree_smoothed_count_le_127
-- name    : Helfgott.squarefree_smoothed_count_le_127
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T14:29:18.54809+00:00
-- url     : https://prove2.me/theorems/ae3a6c0f-705c-4818-a63a-eb1a09cce73c
-- title:
--   Sharp 1.27 bound for the smoothed squarefree counting function
-- statement:
--   For every real x>=0, the number of squarefree positive integers n<=x plus (x^2/2) times the sum of 1/n^2 over squarefree n>x is at most 1.27*x. The endpoint x=0 is included. This is the explicit smoothed squarefree counting estimate used in Helfgott section 4.1.1 to control the error in the actual Vaughan Type II cancellation reduction.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, equations (4.16)-(4.17), https://arxiv.org/abs/1205.5252. Original complete Lean proof by the exact squarefree reciprocal-square series, finite exact rational checks, exclusion of multiples of four, and integral/telescoping tail bounds. Written by Codex.

import Mathlib
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_smoothed_count_le_127  (x : ℝ) (hx : 0≤x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if ⌊x⌋₊<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by sorry

end Helfgott
