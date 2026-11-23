-- Prove2me | Theorems.Thm_NoHair_reflected_negative_static_tails_are_completion_neighborhoods
-- name    : NoHair.reflected_negative_static_tails_are_completion_neighborhoods
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:16:28.357147+00:00
-- url     : https://prove2.me/theorems/677e2dea-0689-42cf-87a4-973928b2e507
-- title:
--   The negative radial tails form neighborhoods at the completion point
-- statement:
--   In the metric completion, every neighborhood of the added point contains a sufficiently far negative tail, and adjoining the point to any such tail gives a neighborhood. A fixed metric ball misses the far positive end. A simultaneously truncated compact core stays a positive distance from the new point.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.reflected_negative_static_tails_are_completion_neighborhoods (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
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
      Tendsto (fun x : ADMPoint => ((d.side false).symm x : UniformSpace.Completion d.carrier)) (cocompact ADMPoint) (𝓝 p) ∧
      (∀ w : UniformSpace.Completion d.carrier, w = p ∨ ∃ q : d.carrier, (q : UniformSpace.Completion d.carrier) = w) ∧
      ∀ R : ℝ, ({p} ∪ ((fun x : ADMPoint => ((d.side false).symm x : UniformSpace.Completion d.carrier)) ''
        {x : ADMPoint | R<‖x‖})) ∈ 𝓝 p := by sorry
