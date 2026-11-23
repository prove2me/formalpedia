-- Prove2me | Theorems.Thm_NoHair_reflected_static_double_metric_completion_one_point
-- name    : NoHair.reflected_static_double_metric_completion_one_point
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:13:26.134877+00:00
-- url     : https://prove2.me/theorems/a7290036-7b69-49cb-a945-824b3a1b409d
-- title:
--   The metric completion of a reflected static double adds exactly its one negative-end point
-- statement:
--   The negative end converges to a new point. The lower differential bound on the positive chart makes the positive coordinate radius bounded on every metric ball. Excising the two far tails leaves a compact core. A completion point different from the negative pole has a neighborhood avoiding the negative tail and bounded in the intrinsic distance, so it belongs to the closed image of such a compact core.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.reflected_static_double_metric_completion_one_point (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    ∃ p : UniformSpace.Completion d.carrier, (∀ q : d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) ∧
      Tendsto (fun x : ADMPoint => ((d.side false).symm x : UniformSpace.Completion d.carrier))
        (cocompact ADMPoint) (𝓝 p) ∧
      ∀ w : UniformSpace.Completion d.carrier, w = p ∨ ∃ q : d.carrier, (q : UniformSpace.Completion d.carrier) = w := by sorry
