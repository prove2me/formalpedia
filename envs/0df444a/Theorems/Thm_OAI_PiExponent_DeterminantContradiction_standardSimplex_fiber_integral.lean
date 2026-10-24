-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_fiber_integral
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:14:20.724793+00:00
-- url     : https://prove2.me/theorems/bf3a73f2-3c87-4f59-b457-49c055fda432
-- title:
--   Identify simplex fibers on the integration interval
-- statement:
--   Over t in [0,A], the fiber of the (m+1)-dimensional simplex at first coordinate t is exactly the m-dimensional nonnegative simplex with cutoff A-t. The interval restriction supplies 0 ≤ t and t ≤ A; the sum decomposition handles the cutoff, including m = 0 and the endpoints.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_integral (m : Nat) (A : Real) :
    (∫ t in Set.Icc (0 : Real) A,
      (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈
        {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A}}).toReal) =
      ∫ t in Set.Icc (0 : Real) A,
        (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧
          ∑ i : Fin m, y i ≤ A - t}).toReal := by sorry
