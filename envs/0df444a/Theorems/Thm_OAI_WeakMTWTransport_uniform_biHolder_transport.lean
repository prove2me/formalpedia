-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_uniform_biHolder_transport
-- name    : OAI.WeakMTWTransport.uniform_biHolder_transport
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.769789+00:00
-- url     : https://prove2.me/theorems/628e07f1-db30-4b2b-9208-3a6c811c5dbc
-- statement:
--   The theorem states that, for dimension n ≥ 2 and a compact, connected metric space M carrying a smooth (C^∞) n-dimensional manifold structure modeled on Euclidean space ℝⁿ, a C^∞ Riemannian bundle metric on its tangent spaces, the Riemannian-manifold compatibility with its metric, and the Borel σ-algebra, suppose the weak MTW condition holds. Weak MTW means that for every point x, every vector p in the injectivity domain at x (vectors p for which the geodesic from x with initial velocity a·p still realizes the distance, dist = a‖p‖, for some a > 1), and all tangent vectors ξ, η at x that are orthogonal, the Ma–Trudinger–Wang quantity is nonnegative; that quantity is −3/2 times the iterated second derivatives in t and s of the cost c(y,z) = dist(y,z)²/2 evaluated at exp_x(tξ) and exp_x(p + sη), at t = s = 0. Let 0 < lam ≤ cap be reals such that at least one admissible density exists. A density ρ : M → ℝ is admissible when it is almost-everywhere measurable and integrable with respect to the calibrated volume measure metricVolume (Hausdorff measure of dimension n rescaled to agree with Lebesgue measure on Euclidean space), has integral 1, and satisfies lam ≤ ρ ≤ cap almost everywhere. Then there exist α with 0 < α ≤ 1 and C ≥ 0 such that for all admissible densities ρ0 and ρ1 there is a homeomorphism T of M that is an optimal map from ρ0 to ρ1 for the quadratic cost, that is, a measurable map pushing the measure ρ0·vol forward to ρ1·vol and minimizing ∫ cost(x,S x) ρ0(x) dvol among all such measurable maps S. Moreover, every optimal map S from ρ0 to ρ1 agrees with T almost everywhere with respect to ρ0·vol, and both T and its inverse are Hölder with the same exponent α and constant C: dist(Tx,Tx') ≤ C·dist(x,x')^α and dist(T⁻¹y,T⁻¹y') ≤ C·dist(y,y')^α. The exponent α and constant C depend only on M, lam and cap, not on ρ0 and ρ1. The statement is admitted without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BiholderTransport.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BiholderTransport.lean; bytes 4068..5376
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BiholderTransport

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle

open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport

/-- Uniform bi-Hölder optimal transport for all densities between fixed bounds
on a compact connected smooth Riemannian manifold satisfying weak MTW. -/
theorem uniform_biHolder_transport
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ, Model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Model n) ∞ (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsRiemannianManifold 𝓘(ℝ, Model n) M]
    [MeasurableSpace M] [BorelSpace M]
    (hmtw : WeakMTW (n := n) (M := M))
    (lam cap : ℝ) (hlam : 0 < lam) (hcap : lam ≤ cap)
    (hclass : ∃ rho : M → ℝ, AdmissibleDensity (metricVolume n) lam cap rho) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T := by
  sorry

end WeakMTWTransport
end
end OAI
