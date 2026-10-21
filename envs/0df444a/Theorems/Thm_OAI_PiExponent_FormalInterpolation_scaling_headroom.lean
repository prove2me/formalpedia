-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaling_headroom
-- name    : OAI.PiExponent.FormalInterpolation.scaling_headroom
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:37:47.84766+00:00
-- url     : https://prove2.me/theorems/b7d3dcac-bc38-469b-8eaa-40c2730ed55c
-- title:
--   Rational headroom for finitely many strict scaling bounds
-- statement:
--   Given two strict scalar bounds and finitely many strict coordinate bounds, there is a rational factor above one that preserves all the bounds. This isolates the finite continuity and rational-density argument from the target.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.scaling_headroom
    (m : Nat) (A B : Real) (c d : Fin m -> Real)
    (hA : A < 1) (hB : B < 1)
    (hcd : forall i, c i < d i) :
    exists q : Rat, 1 < q /\
      ((q : Real) ^ (m + 1) * A < 1) /\
      ((q : Real) ^ m * B < 1) /\
      (forall i, (q : Real) * c i < d i) := by sorry
