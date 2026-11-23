-- Prove2me | Theorems.Thm_NoHair_positive_static_end_chart_realizes_zero_adm_end
-- name    : NoHair.positive_static_end_chart_realizes_zero_adm_end
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:48:31.391474+00:00
-- url     : https://prove2.me/theorems/d688497b-5580-4f18-81ff-f50fc792a464
-- title:
--   The positive physical chart supplies the zero-mass ADM end on a smooth scalar-flat filling
-- statement:
--   Restrict the physical chart to a sufficiently far coordinate exterior. The positive conformal metric has the required first two orders of asymptotic falloff, and its ADM flux tends to zero. On this open exterior the Riemannian coefficients agree with the physical metric, including their derivatives. Compact complements of all far truncations make this the unique end.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.positive_static_end_chart_realizes_zero_adm_end (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (f : OpenPartialHomeomorph Q ADMPoint) (target : f.target=Ω)
    (forward : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f f.source)
    (backward : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm f.target)
    (coeff : ∀ x ∈ Ω, riemannianEndCoeffs f.symm x = staticPositiveMetric N h x)
    (flat : ∀ t ∈ atlas ADMPoint Q, ∀ x ∈ t.target, spatialScalarCurvature (riemannianEndCoeffs t.symm) x = 0)
    (farCompact : ∃ A : ℝ, 0<A ∧ ∀ t:ℝ, A≤t → IsCompact (f.symm '' {x : ADMPoint | t<‖x‖})ᶜ)
    (mass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    HasScalarFlatZeroADMEnd Q := by sorry
