-- Prove2me | Theorems.Thm_NoHair_smooth_static_point_chart_is_topological_chart_of_completion
-- name    : NoHair.smooth_static_point_chart_is_topological_chart_of_completion
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:16:31.011985+00:00
-- url     : https://prove2.me/theorems/2e26526d-ebb4-4bca-af18-e8175d0fd2a4
-- title:
--   The given smooth negative-end cap extends to a topological coordinate chart of the metric completion
-- statement:
--   Away from the pole, compose the cap parametrization with the negative-sheet chart and the open inclusion of the reflected manifold in its completion. Send the center of the parameter ball to the new completion point. Negative tails form its neighborhoods. The end behavior of the parametrization and its inverse then proves continuity in both directions at the added point.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.smooth_static_point_chart_is_topological_chart_of_completion (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    ∃ (p : UniformSpace.Completion d.carrier) (e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier)),
      (∀ q : d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) ∧
      e.source = Metric.ball 0 a.radius ∧ e 0=p ∧
      (∀ y ∈ a.change.source, e y = ((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier)) := by sorry
