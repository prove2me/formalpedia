-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_source_main
-- name    : OAI.PosteriorReplicas.source_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:06.259986+00:00
-- url     : https://prove2.me/theorems/2a8fcd5f-725d-4da3-95f5-ce625b0856e5
-- statement:
--   The theorem states that eight properties from the PosteriorReplicas development hold simultaneously. Throughout, Vec d is d-dimensional Euclidean space, sphereLaw d is the normalized uniform measure on the unit sphere, and a signal s drawn from a prior p is observed through k independent standard Gaussian rows A_i with labels <A_i,s>, which a Markov kernel κ compresses into a message W in {1,...,N}; the information is the conditional mutual information I(s;W | fresh data), computed from ℓ further Gaussian rows and their labels, and H(W) is the entropy of the message. (1) EqualLabelMeasureIdentity: for 1≤k, 1≤m, k+m≤d−2, a spherical or Gaussian base law and a measurable f≥0 bounded by a finite constant, the tilted equal-label functional (projected label density to the power m+1 times the integral of H over m+1 tuples drawn from the tilted fibers) is finite for H=1, and for every measurable H≥0 it equals an explicit Gaussian-normalized integral over (m+1)-tuples from the f-tilted base law, weighted by the inverse k-th power of the affine volume of the tuple, with rows constrained to be orthogonal to the tuple's differences. (2) EqualLabelVersions: under the same hypotheses, the projected density and its ball-limit and Gaussian-smoothing liminf versions are measurable; for linearly independent rows the label law has the projected density and the three versions agree almost everywhere; and for almost every tuple, almost every constrained row family is linearly independent, gives equal labels to all tuple points, has (in the spherical case) lifted label norm below 1, and has projected density positive, finite and equal to both versions. (3) GaussianReplicaBlock: there are C>0 and d₀ such that for d≥d₀, with k=2⌊d/16⌋, t=k+1, ℓ=4k, any prior with density f, 0≤f≤L, with respect to sphereLaw, and any N≥1 and kernel on k rows and labels, the information is at most H(W)/t + C d + C log(2+log L). (4) DistanceReplicaBlock: for large d, k=⌊d/16⌋, ℓ=⌊d/2⌋ and density bound e^b with b≥0, it is at most H(W)/⌊d/8⌋ + C(d + b/d). (5) HaarReplicaBlock: for d≥64, a state law q on Vec d×{1..V} whose first marginal is sphereLaw, a kernel from the state and k=⌊d/16⌋ rows with labels to a message in {1..W}, and ℓ=⌊d/4⌋ Haar (Gram-Schmidt orthonormalized Gaussian) rows, the information is at most (H(V,W)−H(V))/(k+1) + C d + log(1+C d+H(V)) + C(H(V)+log d)/d². (6) SyntheticReplicaBlock: for d≥16, density bound L≥1 and a deterministic measurable message z of ⌊d/8⌋ rows and labels, with ℓ=⌊d/2⌋, the information is at most log N/⌊d/8⌋ + C(d+log(1+log L)). (7) IncidenceReplicaBlock: for large d, k=⌊d/16⌋, ℓ=⌊d/4⌋ and density bound F≥1, it is at most log N/k + C d + C log(1+log F). (8) KernelSubquadraticMemory: there is c>0 such that for every memory size M(d)=o(d²), for all large d, T and ε in (0,1/10], any randomized sequential learner with 2^M(d) states, seeing T Gaussian samples with noiseless linear labels of a uniform sphere signal and whose uniform-sphere success probability of angular error at most ε is at least 2/3, must have T ≥ c d log(1/ε).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PosteriorReplicas.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PosteriorReplicas.lean; bytes 18720..18992
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PosteriorReplicas

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

namespace PosteriorReplicas

universe u

theorem source_main : EqualLabelMeasureIdentity ∧ EqualLabelVersions ∧
    GaussianReplicaBlock ∧ DistanceReplicaBlock ∧ HaarReplicaBlock ∧
    SyntheticReplicaBlock ∧ IncidenceReplicaBlock ∧
    PosteriorRegression.KernelSubquadraticMemory.{u} := by
  sorry

end PosteriorReplicas
end OAI
