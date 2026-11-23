-- Prove2me | Theorems.Thm_NoHair_riemannian_metric_gluing_on_prescribed_smooth_static_completion_atlas
-- name    : NoHair.riemannian_metric_gluing_on_prescribed_smooth_static_completion_atlas
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:59:36.891019+00:00
-- url     : https://prove2.me/theorems/94ad0b8e-4ef4-446e-91f6-85a21d3b2acb
-- title:
--   Glue the Riemannian tensor and preserve the intrinsic distance on the specified smooth filling
-- statement:
--   The smooth atlas already contains the cap coordinates and all lifted charts from the punctured manifold. The remaining metric argument glues the smooth cap tensor to the reflected tensor, verifies equality of the length distance with the completion distance, and transfers the local scalar curvature and signed-lapse equations.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.riemannian_metric_gluing_on_prescribed_smooth_static_completion_atlas (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
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
    ∀ ch : ChartedSpace ADMPoint (UniformSpace.Completion d.carrier), letI := ch
      ∀ sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ (UniformSpace.Completion d.carrier), letI := sm
      (e.symm ∈ atlas ADMPoint (UniformSpace.Completion d.carrier) ∧
      ∀ z ∈ atlas ADMPoint d.carrier, ∃ z' ∈ atlas ADMPoint (UniformSpace.Completion d.carrier),
        z'.source = (fun q:d.carrier => (q:(UniformSpace.Completion d.carrier))) '' z.source ∧ z'.target = z.target ∧
        (∀ q:d.carrier, z' (q:(UniformSpace.Completion d.carrier))=z q) ∧ (∀ x:ADMPoint, z'.symm x=(z.symm x:(UniformSpace.Completion d.carrier)))) →
      ∃ rb : RiemannianBundle (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q), letI := rb
      IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : (UniformSpace.Completion d.carrier) => TangentSpace 𝓘(ℝ,ADMPoint) q) ∧
      IsRiemannianManifold 𝓘(ℝ,ADMPoint) (UniformSpace.Completion d.carrier) ∧
      (∀ t ∈ atlas ADMPoint (UniformSpace.Completion d.carrier), ∀ x ∈ t.target, spatialScalarCurvature (riemannianEndCoeffs t.symm) x = 0) ∧ ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 2 L ({p}ᶜ) ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f f.source ∧
      ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm f.target ∧
      (∀ x ∈ Ω, riemannianEndCoeffs f.symm x = staticPositiveMetric N h x) ∧
      (∀ e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier),
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source →
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target →
    ∀ x ∈ e.source, e x ≠ p → L (e x) ≠ 0 →
      staticWeightedLapseDivergence (riemannianEndCoeffs e) (L ∘ e) x = 0) := by sorry
