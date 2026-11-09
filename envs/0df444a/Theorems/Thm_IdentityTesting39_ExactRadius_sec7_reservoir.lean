-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec7_reservoir
-- name    : IdentityTesting39.ExactRadius.sec7_reservoir
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:00.8702+00:00
-- url     : https://prove2.me/theorems/3c494ee2-6482-4120-acaf-df4b1042270b
-- title:
--   §7 — exact reservoir reduction and mixture-preserving lift
-- statement:
--   Let $q$ be diffuse, meaning $q_i<1/8$ for every label, and let $\varepsilon\le1/256$ be a nonempty strict radius. Suppose $n\ge2$ and an all-coordinate feasible witness has objective at most $j$. There exists a reservoir $\mathcal R$ whose mass satisfies $Q_0\in[1/4,3/8)$, with collapsed reference $Q$ having this head as a largest atom and tail mass at least $5/8$. At the identical radius,
--
--   $$\exists\text{ a deficit witness of objective at most }256j,\qquad J_n^-(Q,\varepsilon)\le256j.$$
--
--   For every collapsed probability vector $P$, its reference-proportional lift $p$ is a probability vector and
--
--   $$\operatorname{TV}(p,q)=\operatorname{TV}(P,Q).$$
--
--   The lift is measurable. Every normalized collapsed prior lifts to a normalized prior, and the TV distance of its lifted Poisson mixture from the original null is at most the corresponding collapsed mixture distance from the collapsed null. Thus the reduction preserves both the statistical comparison and the exact radius.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: one head plus labels outside the reservoir → Option of the subtype of labels outside the reservoir; reason: this is the exact quotient label set; the lift is explicitly constructed
--   - encoding: refinement of observations is a fixed Markov kernel → measurability of the explicit lift and contraction of the corresponding Poisson mixtures; reason: Poisson head refinement is independent thinning, so it yields the same observation experiment
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.10, §7, display (13) and reservoir reduction, lift continuing on p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_Reservoir

open MeasureTheory
open scoped BigOperators

namespace IdentityTesting39.ExactRadius

/-- §7, (13) and the lift, printed pp.10–11 / PDF pp.11–12. -/
theorem sec7_reservoir {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε n j : ℝ) (x : MomentFamily ι)
    (hq : ProbabilityVector q) (hε : StrictRadius q ε)
    (hdiff : ∀ i, q i < 1/8) (hsmall : ε ≤ 1/256) (hn : 2 ≤ n)
    (hx : x ∈ feasibleMoments q ε .all) (hcost : objective q .all n x ≤ j) :
    ∃ R : Finset ι,
      1/4 ≤ ∑ i ∈ R, q i ∧ (∑ i ∈ R, q i) < 3/8 ∧
      ProbabilityVector (collapsedReference q R) ∧
      Largest (collapsedReference q R) none ∧
      5/8 ≤ 1-collapsedReference q R none ∧
      (∃ y ∈ feasibleMoments (collapsedReference q R) ε (.deficit none),
        objective (collapsedReference q R) (.deficit none) n y ≤ 256*j) ∧
      programValue (collapsedReference q R) ε n (.deficit none) ≤ 256*j ∧
      Measurable (liftVector q R) ∧
      (∀ P : CollapsedLabels R → ℝ, ProbabilityVector P →
        ProbabilityVector (liftVector q R P) ∧
        FoundationsRL.GeneralDM.totalVariationDiscrete (liftVector q R P) q = FoundationsRL.GeneralDM.totalVariationDiscrete P (collapsedReference q R)) ∧
      (∀ π : Measure (CollapsedLabels R → ℝ), NormalizedPrior π →
        NormalizedPrior (liftPrior q R π) ∧
        MarkovChainCLT.tvDist (poissonMixture n (liftPrior q R π)) (poissonExperiment n q) ≤
          MarkovChainCLT.tvDist (poissonMixture n π) (poissonExperiment n (collapsedReference q R))) := by sorry

end IdentityTesting39.ExactRadius
