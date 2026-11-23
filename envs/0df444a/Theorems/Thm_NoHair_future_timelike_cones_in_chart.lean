-- Prove2me | Theorems.Thm_NoHair_future_timelike_cones_in_chart
-- name    : NoHair.future_timelike_cones_in_chart
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:13:42.268807+00:00
-- url     : https://prove2.me/theorems/ecbf54b8-1e48-4e76-aaa4-d4591c5dda47
-- title:
--   Future timelike directions form an open family of convex cones in spacetime charts
-- statement:
--   For a smooth Lorentzian metric and a continuous timelike time orientation, the pairs consisting of a chart point and a future timelike coordinate vector form an open subset of $\mathbb R^4\times\mathbb R^4$. At each chart point the set of such vectors is convex. These properties allow future-directed timelike corners to be rounded while keeping the velocity strictly inside the cone.
-- source:
--   B. O’Neill, Semi-Riemannian Geometry (Academic Press, 1983), Chapter 5, timecones and timelike vectors, and Chapter 14, chronological relations. The curve regularity here is that of the mission definition NoHair.IsFutureTimelikeCurveIn, https://prove2.me/theorems/d3c7be7a-309a-40fd-b177-28ba5a1b316c .

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.future_timelike_cones_in_chart {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] (g : BilinField M) (T : VecField M)
    (hg : IsLorentzian g) (hs : IsSmoothBilinField g) (hT : IsTimeOrientation g T) (p : M) :
    let e := chartAt E4 p
    let K := {z : E4 × E4 | z.1 ∈ e.target ∧
      IsFutureTimelike g T (e.symm z.1) ((mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) e.symm z.1) z.2)}
    IsOpen K ∧ ∀ y ∈ e.target, Convex ℝ {v : E4 | (y,v) ∈ K} := by
  sorry
