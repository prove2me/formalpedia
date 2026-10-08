-- Prove2me | Theorems.Thm_OAI_WeakHessian_every_geodesic
-- name    : OAI.WeakHessian.every_geodesic
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.446768+00:00
-- url     : https://prove2.me/theorems/233da58f-705b-47c5-9108-df17f0b21990
-- statement:
--   The theorem states that, on a complete separable metric space X with Borel σ-algebra and a Borel measure m with full support (positive measure on every nonempty open set) and finite on bounded sets, satisfying the defined RCD(K,N) condition for real K and N>1, the following holds. Here RCD(K,N) means the defined curvature-dimension condition CD(K,N), phrased through optimal dynamical plans of geodesics with distortion coefficients and Rényi entropy integrals, together with quadratic Cheeger energy (the parallelogram identity for Cheeger energy on finite-energy functions). Let F be bounded and globally Lipschitz and let G be bounded and continuous, and suppose (F,G) satisfies the weak Hessian upper bound: for every compactly supported test function g (bounded, globally Lipschitz, in the Laplacian domain with Sobolev Laplacian) and every nonnegative, compactly supported, globally Lipschitz h, the weak Hessian of F in direction g tested against h is at most the integral of h·G·Γ(g,g) with respect to m, where Γ is the polarized minimal weak gradient pairing. Then for every constant-speed minimizing geodesic σ:[0,1]→X, including constant curves, the second distributional derivative of F∘σ is bounded by G∘σ in the following sense. For every smooth, nonnegative, compactly supported φ whose support lies in (0,1), the integral over [0,1] of F(σ(t))φ''(t) is at most d(σ(0),σ(1))² times the integral over [0,1] of G(σ(t))φ(t).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeakHessian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeakHessian.lean; bytes 9663..10266
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_WeakHessian

namespace OAI

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

/-- A weak upper Hessian bound controls the second distributional derivative
along every constant-speed minimizing geodesic. -/
theorem every_geodesic [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (m : Measure X) (K N : ℝ) (hN : 1 < N)
    (hfull : FullSupport m) (hfinite : FiniteOnBoundedSets m) (hrcd : RCD m K N)
    (F G : X → ℝ) (hFbound : BoundedFunction F) (hFlip : GloballyLipschitz F)
    (hGbound : BoundedFunction G) (hGcont : Continuous G)
    (hHess : WeakHessianUpperBound m F G)
    (σ : Curve X) (hσ : IsGeodesic σ) : CurveSecondDerivativeBound F G σ := by
  sorry

end WeakHessian
end
end OAI
