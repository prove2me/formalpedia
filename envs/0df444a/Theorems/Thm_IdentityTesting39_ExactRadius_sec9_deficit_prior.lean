-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec9_deficit_prior
-- name    : IdentityTesting39.ExactRadius.sec9_deficit_prior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:56.984202+00:00
-- url     : https://prove2.me/theorems/90da3474-1e8c-4bdb-aec4-1070cbbe7764
-- title:
--   §9 — deficit-preserving normalized prior with constant far mass
-- statement:
--   There is an absolute $j_0>0$. For every finite probability reference $q$ and nonempty strict radius $\varepsilon\ge1/256$, let $n\ge1$ and suppose an all-coordinate feasible moment witness has objective at most $j_0$. There is a probability prior $\pi$, almost surely on probability vectors, such that with $\gamma=1/152$,
--
--   $$\pi\{p:\operatorname{TV}(p,q)>\varepsilon\}\ge\gamma/2,\qquad \operatorname{TV}\!\left(\mathbb E_\pi\bigotimes_i\operatorname{Poi}(np_i),\bigotimes_i\operatorname{Poi}(nq_i)\right)\le\gamma/4.$$
--
--   This assertion holds for every reference, including those with a large atom or zero coordinates. It gives constant far mass, rather than concentration entirely outside the radius, and keeps the entire prior in the observation mixture. The threshold is chosen before the reference, radius, intensity and witness.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: every draw is a probability vector and prior mass is assigned to the strict event → a normalized measure almost surely on the simplex, with extended nonnegative event probability; reason: null sets do not change priors or their observation mixtures
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.13, §9, displays (15), (18), (19); standing hypotheses on p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open MeasureTheory
open scoped ENNReal

namespace IdentityTesting39.ExactRadius

/-- §9, (15),(18),(19), printed pp.12–13 / PDF pp.13–14; applies to every reference. -/
theorem sec9_deficit_prior :
    ∃ j₀ : ℝ, 0 < j₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε n : ℝ)
      (x : MomentFamily ι),
      ProbabilityVector q → StrictRadius q ε → 1/256 ≤ ε → 1 ≤ n →
      x ∈ feasibleMoments q ε .all → objective q .all n x ≤ j₀ →
      ∃ π : Measure (ι → ℝ), NormalizedPrior π ∧
        ENNReal.ofReal ((1/152 : ℝ)/2) ≤ farMass q ε π ∧
        MarkovChainCLT.tvDist (poissonMixture n π) (poissonExperiment n q) ≤ (1/152 : ℝ)/4 := by sorry

end IdentityTesting39.ExactRadius
