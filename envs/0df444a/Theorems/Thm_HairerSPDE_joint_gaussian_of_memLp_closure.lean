-- Prove2me | Theorems.Thm_HairerSPDE_joint_gaussian_of_memLp_closure
-- name    : HairerSPDE.joint_gaussian_of_memLp_closure
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T06:09:39.362217+00:00
-- url     : https://prove2.me/theorems/51a7b245-ad90-43f0-8c27-fb4bcb2f8fd5
-- title:
--   Joint Gaussianity of duals with an L2-closure representer
-- statement:
--   Let B be a separable Banach space, mu a centred Gaussian Borel measure, and h' in L^2(mu) lying in the closed span R_mu of the continuous duals (orthogonal to everything orthogonal to all duals). Then for every continuous linear functional L and all real a, b, the real random variable x -> a*L(x) + b*h'(x) is centred Gaussian with its own variance. In particular (L, h') is jointly centred Gaussian. This is Hairer Proposition 4.40 for the first chaos: L^2-limits of continuous linear functionals remain centred Gaussian, applied to the linear combinations aL + bh' which stay in R_mu.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Proposition 4.40 and Theorem 4.44, used in the proof of Proposition 4.45.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem joint_gaussian_of_memLp_closure {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'orth : (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0)) :
    ∀ (L : StrongDual ℝ B) (a b : ℝ),
      μ.map (fun x => a * L x + b * h' x) =
        gaussianReal 0 ((ProbabilityTheory.variance (fun x => a * L x + b * h' x) μ).toNNReal) := by sorry

end HairerSPDE
