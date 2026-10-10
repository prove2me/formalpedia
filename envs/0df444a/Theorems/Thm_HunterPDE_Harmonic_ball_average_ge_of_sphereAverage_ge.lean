-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_ball_average_ge_of_sphereAverage_ge
-- name    : HunterPDE.Harmonic.ball_average_ge_of_sphereAverage_ge
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T14:24:23.449344+00:00
-- url     : https://prove2.me/theorems/72d15790-a4ed-4f0c-8efe-edca4539071f
-- title:
--   Lower spherical mean bounds imply a lower ball mean bound
-- statement:
--   Let n ≥ 1, r > 0, and let u be continuous on the closed ball of radius r centered at x. If the normalized average of u on every concentric sphere of radius t with 0 < t ≤ r is at least a real constant c, then the normalized average on the open ball of radius r is also at least c. No pointwise lower bound on u is required. The proof uses polar integration of u minus c. This is the polar integration step in Hunter’s Theorem 2.5.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, p. 22, Theorem 2.5; p. 20, equation (2.4) and polar integration in the proof of Theorem 2.1. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set Metric
open HunterPDE.Harmonic

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem HunterPDE.Harmonic.ball_average_ge_of_sphereAverage_ge {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r c : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (Metric.closedBall x r))
    (havg : ∀ t ∈ Ioc 0 r, c ≤ sphereAverage u x t) :
    c ≤ (⨍ y in Metric.ball x r, u y) := by sorry
