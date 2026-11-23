-- Prove2me | Theorems.Thm_NoHair_smooth_completion_atlas_from_reflected_static_point_chart
-- name    : NoHair.smooth_completion_atlas_from_reflected_static_point_chart
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:59:28.354119+00:00
-- url     : https://prove2.me/theorems/7fcb3acb-deb1-4aca-9430-eaf4e59a53c0
-- title:
--   The negative cap and all reflected charts form a smooth atlas on the metric completion
-- statement:
--   Lift every reflected atlas chart through the open inclusion into the completion, and add the inverse of the cap parametrization as a chart containing the pole. Between two old charts the transition is unchanged. On a mixed overlap the transition factors through the smooth negative-sheet parametrization and the smooth change of cap coordinates. The inverse transition factors through their inverses. These charts cover the entire completion and are smoothly compatible.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.smooth_completion_atlas_from_reflected_static_point_chart (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (p : UniformSpace.Completion d.carrier) (off : ∀ q:d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p)
    (exhaust : ∀ w : UniformSpace.Completion d.carrier, w=p ∨ ∃ q:d.carrier, (q : UniformSpace.Completion d.carrier)=w)
    (e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier))
    (ball : e.source=Metric.ball 0 a.radius) (center : e 0=p)
    (agrees : ∀ y ∈ a.change.source, e y=((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier)) :
    ∃ ch : ChartedSpace ADMPoint (UniformSpace.Completion d.carrier), letI := ch
      IsManifold 𝓘(ℝ,ADMPoint) ∞ (UniformSpace.Completion d.carrier) ∧ e.symm ∈ atlas ADMPoint (UniformSpace.Completion d.carrier) ∧
      ∀ z ∈ atlas ADMPoint d.carrier, ∃ z' ∈ atlas ADMPoint (UniformSpace.Completion d.carrier),
        z'.source = (fun q:d.carrier => (q:(UniformSpace.Completion d.carrier))) '' z.source ∧ z'.target = z.target ∧
        (∀ q:d.carrier, z' (q:(UniformSpace.Completion d.carrier))=z q) ∧ (∀ x:ADMPoint, z'.symm x=(z.symm x:(UniformSpace.Completion d.carrier))) := by sorry
