-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nat_between_rat_and_succ
-- name    : OAI.PiExponent.FormalInterpolation.exists_nat_between_rat_and_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:14:43.074265+00:00
-- url     : https://prove2.me/theorems/105f51c5-596b-421c-82ed-4bf157c648cb
-- title:
--   A natural lies between a positive rational and its successor
-- statement:
--   For each positive rational q, produce a natural B in [q, q+1). This isolates the rounding step needed to turn the geometric dependency’s one-unit strict cutoff slack into the parent’s natural cutoff.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Floor

theorem OAI.PiExponent.FormalInterpolation.exists_nat_between_rat_and_succ (q : Rat) (hq : 0 < q) : ∃ B : Nat, (q : Real) ≤ (B : Real) ∧ (B : Real) < (q : Real) + 1 := by sorry
