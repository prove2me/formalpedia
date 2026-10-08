-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_full_current_main_scope
-- name    : OAI.SubsphereCurrent.full_current_main_scope
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.565898+00:00
-- url     : https://prove2.me/theorems/9f2531b4-7c3e-4758-a9d9-e7156556b3f3
-- statement:
--   The theorem states (its proof is admitted in the source) that the conjunction CurrentMainScope of six statements holds, with universe parameters u, v, w for the seed space, the finite state index type, and the ambient inner product space respectively. Throughout, a learner sees T Gaussian rows x_i in R^d together with the inner products <x_i,s> with an unknown unit vector s, uses a finite-state randomized update rule (possibly with an extra random seed ω drawn from a probability space (Ω,ρ)), and finally outputs a probability measure on the unit sphere; its success at accuracy ε is the probability that the output u satisfies arccos<u,s> ≤ ε. (1) ExplicitPrecision: for every memory-size function M(d) with M(d)=o(d²), there is d₀ such that for all d ≥ d₀, all T, all ε in (0,1/10], and every admissible seeded learner with 2^{M(d)} memory states, if either its success averaged over the uniform sphere is at least 2/3 or its success at every s is at least 2/3, then T ≥ 2^{-16}·d·log₂(1/ε). Admissibility asks that almost every seed's transition rules be a.e.-measurable in the observation and that the fixed-s and uniform-s success functions be a.e.-measurable. (2) RadiusWeightedFullEstimate: there are C ≥ 1 and d₀ such that for d ≥ d₀ two bounds hold. For a finite nonempty index set V with |V| ≤ W (W ≥ 1), measurable kernels κ_v on observations consisting of d/16 rows and their inner products with s, with Σ_v κ_v ≤ 1, measurable weights g_v with values in [0,1], and every n with d/2 ≤ n ≤ d, the weighted norm of the Gaussian-averaged block input Σ_v κ_v g_v is at most W^{1/(d/16)}·C^d times the supremum over v of the weighted norm of g_v with n replaced by n−2. Second, for every probability measure π on the sphere and ε > 0, the weighted norm at level n of s ↦ π{u : arccos<u,s> ≤ ε} is at most C^d·ε^{d/16}. Here the norm at level n of g is the supremum, over affine tests (an n-dimensional subspace, a center orthogonal to it, a radius r > 0 with |center|²+r²=1), of r^{d/16} times the integral of g over the normalized sphere of the subspace mapped to center + r·(point). (3) HalfPrecision: the same conclusion as (1), for the same memory range and ε range but with only the hypothesis that uniform success is at least 1/2, and with a constant c > 0 in place of 2^{-16}, so that c·d·log₂(1/ε) ≤ T. (4) AllAffineFullEstimate (an estimate for streams with finitely many states): for large d, k with (d+1)/2+2k ≤ d, W ≥ 1, a state set J with |J| ≤ W and W^{1/(d/8)} ≤ 2^d, ε in (0,1/10], seeded streams with k(d/16) steps whose rules are Borel and whose outputs are almost surely unit vectors, any ℓ ≤ k, any start state v, any n ≥ (d+1)/2+2ℓ and any affine test A of dimension n, the success, averaged over the sphere of A's subspace, the seed and ℓ(d/16) Gaussian rows, of the suffix stream started at v in producing an estimate within angle ε of the point A.point(s), is at most ((16·1000^{32ℓ}·ε)/radius(A))^{2(d/32)}. (5) Fixed.DimensionEstimate: there are C ≥ 2 and d₀ such that for d ≥ d₀, j, and m with d/2+2j ≤ m ≤ d, η > 0, and seeded streams on R^m with 2^{d²} states and j(d/32) steps with almost surely Borel rules, if the Euclidean success function is a.e.-measurable then the success of landing within distance η of s, averaged over the uniform sphere of R^m, the seed and the Gaussian rows, is at most (C^{j+1}η)^{d/32}. (6) For every finite-dimensional real inner product space E with its Borel structure, MixtureEstimate E holds: for subspaces V ≤ N with 1 ≤ dim V < dim N < dim E and every unit e in V, the law of the image of a uniform unit vector of N under a Haar-random orthogonal map of V^⊥ (identity on V) is bounded by 2^{dim E} times the sum of the uniform sphere law on E and a latitude law, where a beta-distributed height with parameters (dim N−dim V)/2 and (dim E−dim N)/2 mixes e with a uniform unit vector of e^⊥ and the result is rotated by a Haar-random orthogonal map of V; for N with dim N ≥ 1 the law with V = 0 equals the uniform sphere law of N; and when dim E ≥ 1, t such rotated vectors from N = E have exactly the joint law of t independent uniform unit vectors of E.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SubsphereCurrent.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SubsphereCurrent.lean; bytes 17965..18037
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SubsphereCurrent

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u v w

namespace SubsphereCurrent

theorem full_current_main_scope : CurrentMainScope.{u,v,w} := by
  sorry

end SubsphereCurrent
end
end OAI
