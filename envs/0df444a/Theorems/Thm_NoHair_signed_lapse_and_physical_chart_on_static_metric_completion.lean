-- Prove2me | Theorems.Thm_NoHair_signed_lapse_and_physical_chart_on_static_metric_completion
-- name    : NoHair.signed_lapse_and_physical_chart_on_static_metric_completion
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:41:49.63137+00:00
-- url     : https://prove2.me/theorems/0c13211a-8667-49ba-8216-2f00eb519ad6
-- title:
--   The extended signed lapse, physical chart, and the two lapse limits of the completed static double
-- statement:
--   The signed lapse extends continuously to the unique new point with value $-1$. Its asymptotic value outside compact sets is $+1$, and it has a zero on the finite horizon. The region where it is positive is precisely the image of the original physical slice, with the original lapse and the same positive-side coordinates.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.signed_lapse_and_physical_chart_on_static_metric_completion (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (p : UniformSpace.Completion d.carrier) (off : ∀ q:d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) :
    ∃ (L : C(UniformSpace.Completion d.carrier, ℝ)) (f : OpenPartialHomeomorph (UniformSpace.Completion d.carrier) ADMPoint),
      (∀ q : d.carrier, L (q : UniformSpace.Completion d.carrier) = d.lapse q) ∧
      L p = -1 ∧
      (∀ z : UniformSpace.Completion d.carrier, z ≠ p → -1 < L z) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : Set (UniformSpace.Completion d.carrier), IsCompact K ∧ ∀ z ∉ K, |L z - 1| ≤ ε) ∧
      (∃ z : UniformSpace.Completion d.carrier, z ≠ p ∧ L z = 0) ∧
      f.source = {z | z ≠ p ∧ 0 < L z} ∧
      f.target = Ω ∧
      (∀ x ∈ Ω, f.symm x = ((d.side true).symm x : UniformSpace.Completion d.carrier)) ∧
      (∀ z ∈ f.source, N (f z) = L z) := by sorry
