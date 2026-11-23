-- Prove2me | Theorems.Thm_NoHair_chronoFuture_transitive
-- name    : NoHair.chronoFuture_transitive
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:20:35.57534+00:00
-- url     : https://prove2.me/theorems/8b99727f-095f-4dbb-99a2-1055eda1d63f
-- title:
--   Chronological precedence is transitive for the mission’s regular timelike curves
-- statement:
--   If $x$ is joined to $y$ and $y$ to $z$ by future timelike curves in a smooth time-oriented Lorentzian spacetime, then $x$ is joined to $z$ by a single future timelike curve. Here the mission requires a globally $C^1$ parametrization, timelike with nonzero velocity on the entire closed parameter interval, including the join.
-- source:
--   B. O’Neill, Semi-Riemannian Geometry (Academic Press, 1983), Chapter 5, timecones and timelike vectors, and Chapter 14, chronological relations. The curve regularity here is that of the mission definition NoHair.IsFutureTimelikeCurveIn, https://prove2.me/theorems/d3c7be7a-309a-40fd-b177-28ba5a1b316c .

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.chronoFuture_transitive {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] (g : BilinField M) (T : VecField M)
    (hg : IsLorentzian g) (hs : IsSmoothBilinField g) (hT : IsTimeOrientation g T)
    {x y z : M} (hxy : y ∈ chronoFuture g T univ x) (hyz : z ∈ chronoFuture g T univ y) :
    z ∈ chronoFuture g T univ x := by
  sorry
