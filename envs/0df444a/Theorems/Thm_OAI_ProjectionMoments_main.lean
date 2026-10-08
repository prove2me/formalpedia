-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_main
-- name    : OAI.ProjectionMoments.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:12.048132+00:00
-- url     : https://prove2.me/theorems/34bbeca3-9b37-46ef-a525-7e31a1320e03
-- statement:
--   The theorem states that the defined proposition MainStatement holds; it is the conjunction of fifteen results about random projections of measures on Euclidean space and about learners that estimate an unknown unit vector s from T noiseless linear observations (x_i, <x_i,s>) with Gaussian x_i using M bits of memory. First, three moment bounds are stated for a lower density (a liminf of averages over small balls) of projected measures. (1) IntegratedFrameMoment: there is C >= 1 such that, for finite measures nu supported in a ball of radius R with all-ball mass bound nu(B(b,t)) <= K t^beta, and for an orthonormal k-frame u under the rotation-invariant frame law, with 1 <= k, 2 <= q, k+q <= d, 0 < beta <= d and beta-k-(q-2) >= 1, if almost every projection of nu to R^k is absolutely continuous, then the coordinate density is measurable, represents the projections almost everywhere, vanishes outside the radius-R ball around the projected centre, and its L^q norm over frames and R^k is at most C^d (C sqrt d)^{k(1-1/q)} K R^{beta-k(1-1/q)}. (2) NormalizedUnitBallMoment: for every D > 0 there is C_D > 0 such that, for d >= 32, k = floor(d/16), nu of total mass at most 1 supported in the unit ball with all-ball mass bound (D^d, exponent (d-1)/2), and absolutely continuous projections under Gaussian rows polar-normalised via the polar decomposition, the normalized density is measurable, represents the projections, vanishes outside the unit ball, and its k-th moment against the normalized unit-ball law and Gaussian rows is at most exp(C_D d k). (3) AllRadiiSphereMoment: with k = floor(d/4), beta = d-1-k, d >= 16, a density f with 0 <= f <= 1 on the sphere, mass bound (K, beta), and the restriction mu of the weighted sphere measure to any closed ball, the same density properties hold for every orthonormal frame, with a k-th moment bound C^d (C sqrt d)^{k(1-1/k)} K R^{beta-k(1-1/k)}. Next come three combinatorial bounds. (4) PositiveCapDomination (d >= 32, k = floor(d/16), alpha = (d-1)/2): sub-probability kernels on frames and labels whose cap-reference masses sum to at most 1 have each kernel's induced cap measure dominated by a nonnegative summable combination of smaller cap measures from a cap dictionary, with weighted coefficient sum at most exp(Cd) times the reference mass to the power 1-1/k. (5) DeterministicOffsetDensity (d >= 16, k = floor(d/8), alpha = d/2): for a measurable 0..1 density h and measurable H inside a ball of radius rho, the Riesz potential of h is finite, the lower density of the restricted weighted measure is a representing density for linearly independent frames, its L^k norm at every offset is at most C^d times the Riesz potential times rho^{alpha-k}, and it vanishes far from the projected centre. (6) AllRadiiBlockBound: fractional blocks of N densities, each with all-ball mass (K, beta), mixed through sub-probability kernels, have all-ball mass at most C^d N^{1/k} K. Then come six quantitative bounds on the success probability of finite-kernel learners (randomized state machines on 2^M memory states, completed so transitions are measurable in the observation), averaged over a probability space of seeds and the uniform sphere, where success means angular error at most epsilon in (0, 1/10]: (7) HaarStreamingCost, with bound C^d eps^k (C^d N*^{1/k})^{(T+k-1)/k}, k = floor(d/4), N* = (k+2)2^M; (8) RieszStreamingCost, with a bound involving eps^{d/2-1} and a logarithmic factor, q = floor(d/8); (9) CapFixedStoppingCost, the success probability of stopping exactly at a fixed time t <= T is at most exp(Cd)(eps/2)^alpha (exp(Cd) 2^{M/k})^{(t+k-1)/k}, d >= 32, k = floor(d/16); (10) CapTotalStoppingCost, the same summed over stopping times with an extra factor T+1; and (11, 12) their asymptotic versions for M(d) = o(d^2). (13) KernelModelBridge: for d >= 3, every completed finite-kernel learner is realized by an admissible measurable-rule learner on a probability space of tapes with identical uniform and fixed-time success. Finally, (14) SubquadraticMemoryWithPointwise: for memory M(d) = o(d^2), eventually in d, any seeded learner achieving success at least 2/3 either on average or pointwise for every s, with epsilon <= 1/10, needs T >= c d log(1/epsilon) samples; and (15) FixedQuadraticMemory: for M <= A0 d^2 and large d, average success at least 2/3 forces T >= c d log(1/epsilon). The theorem is admitted and states all of these as stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionMoments.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProjectionMoments.lean; bytes 29579..29625
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ProjectionMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

universe u

namespace ProjectionMoments

open NoiselessRegression NoiselessRegression.FiniteKernelLearner

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

theorem main : MainStatement.{u} := by
  sorry

end ProjectionMoments
end
end OAI
