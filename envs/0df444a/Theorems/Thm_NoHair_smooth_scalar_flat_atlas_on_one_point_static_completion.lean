-- Prove2me | Theorems.Thm_NoHair_smooth_scalar_flat_atlas_on_one_point_static_completion
-- name    : NoHair.smooth_scalar_flat_atlas_on_one_point_static_completion
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:41:51.680993+00:00
-- url     : https://prove2.me/theorems/457c9d82-572b-4437-92f0-643992fd71e3
-- title:
--   Smooth scalar-flat Riemannian atlas on the actual metric completion of the static double
-- statement:
--   Install the smooth cap and the reflected atlas directly on the one-point metric completion, using their common punctured parametrization. The tensors agree there. The resulting smooth Riemannian metric must induce the given completion distance and have scalar curvature zero, the prescribed positive ADM end, and the stated differential identities for the fixed lapse and physical chart.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.smooth_scalar_flat_atlas_on_one_point_static_completion (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
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
    (agrees : ∀ y ∈ a.change.source, e y=((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier))
    (compactEnd : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ t → IsCompact
      (((fun x : ADMPoint => ((d.side true).symm x : UniformSpace.Completion d.carrier)) '' {x : ADMPoint | t < ‖x‖})ᶜ))
    (L : C(UniformSpace.Completion d.carrier, ℝ)) (f : OpenPartialHomeomorph (UniformSpace.Completion d.carrier) ADMPoint)
    (extension : (∀ q : d.carrier, L (q : UniformSpace.Completion d.carrier) = d.lapse q)) (atPole : L p = -1)
    (source : f.source = {z | z ≠ p ∧ 0 < L z}) (target : f.target=Ω)
    (inverse : (∀ x ∈ Ω, f.symm x = ((d.side true).symm x : UniformSpace.Completion d.carrier))) :
    ∃ ch : ChartedSpace ADMPoint (UniformSpace.Completion d.carrier), letI := ch
      ∃ sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ (UniformSpace.Completion d.carrier), letI := sm
      ∃ rb : RiemannianBundle (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q), letI := rb
      IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q) ∧
      IsRiemannianManifold 𝓘(ℝ,ADMPoint) (UniformSpace.Completion d.carrier) ∧
      HasScalarFlatZeroADMEnd (UniformSpace.Completion d.carrier) ∧ ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 2 L ({p}ᶜ) ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f f.source ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm f.target ∧
      (∀ q ∈ f.source, ∀ v w : TangentSpace 𝓘(ℝ,ADMPoint) q, (∑ i : Fin 3, ∑ j : Fin 3,
      staticPositiveMetric N h (f q) i j *
        (fun z : ADMPoint => z i) (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q v) *
        (fun z : ADMPoint => z j) (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q w)) = inner ℝ v w) ∧
      (∀ e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier),
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source →
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target →
    ∀ x ∈ e.source, e x ≠ p → L (e x) ≠ 0 →
      staticWeightedLapseDivergence (riemannianEndCoeffs e) (L ∘ e) x = 0) := by sorry
