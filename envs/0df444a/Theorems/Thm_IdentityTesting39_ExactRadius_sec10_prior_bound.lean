-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec10_prior_bound
-- name    : IdentityTesting39.ExactRadius.sec10_prior_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:48.075518+00:00
-- url     : https://prove2.me/theorems/aefd6637-218d-4182-a1a9-4856d19c5a3c
-- title:
--   §10 — far prior mass forces a sample lower bound
-- statement:
--   For every $\rho\in(0,1]$ there is $c_\rho>0$, independent of the finite domain, reference, radius, intensity and prior. Let $q$ be a probability reference, $\varepsilon,n>0$, and let $\pi$ be a normalized probability prior with far mass at least $\rho$. If
--
--   $$\pi\{p:\operatorname{TV}(p,q)>\varepsilon\}\ge\rho,\qquad \operatorname{TV}\!\left(\mathbb E_\pi\bigotimes_i\operatorname{Poi}(np_i),\bigotimes_i\operatorname{Poi}(nq_i)\right)\le\rho/2,$$
--
--   then every admissible fixed sample count $m$ satisfies $c_\rho n\le m$. The entire prior, including draws inside the radius, enters the mixture. This converts either full alternative support or constant far mass into a statistical sample lower bound.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - reading: least fixed sample size permitting the two error bounds in §2 → tests are rejection-probability functions with values in [0,1]; reason: Appendix A explicitly uses randomized testers and §4 uses internal Poisson-simulation randomness
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: N* = Ω_ρ(n) → the lower inequality holds for every admissible sample count; reason: does not rely on an empty-set infimum; c is chosen after ρ and before all other data
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.14, §10, from Poisson priors to sample size; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open MeasureTheory
open scoped ENNReal

namespace IdentityTesting39.ExactRadius

/-- §10, printed p.14 / PDF p.15: a prior's far mass is not assumed to be one. -/
theorem sec10_prior_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (ι : Type) [Fintype ι] (q : ι → ℝ) (ε n : ℝ) (π : Measure (ι → ℝ)),
      ProbabilityVector q → 0 < ε → 0 < n → NormalizedPrior π →
      ENNReal.ofReal ρ ≤ farMass q ε π →
      MarkovChainCLT.tvDist (poissonMixture n π) (poissonExperiment n q) ≤ ρ/2 →
      ∀ m ∈ admissibleSizes q ε, c*n ≤ (m : ℝ) := by sorry

end IdentityTesting39.ExactRadius
