-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_9_10_11_poisson
-- name    : IdentityTesting39.ExactRadius.eq_9_10_11_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:33.063252+00:00
-- url     : https://prove2.me/theorems/00f0057d-b869-442f-8b33-bbb71a6553ba
-- title:
--   §5, (9)–(11) — Poisson mixtures and mean comparison
-- statement:
--   For a nonnegative probability law $\mu$ with finite second moment, mean $r$ and variance $v$, and $n\ge0$, its scalar Poisson mixture is a probability measure and
--
--   $$\operatorname{TV}(\mathbb E\operatorname{Poi}(nU),\operatorname{Poi}(nr))\le n^2v.$$
--
--   For each $c>0$ there is $C_c>0$, uniform over the law, $n$ and support bound $R$, such that if $n,r>0$, $|U-r|\le R$ almost surely and $nR^2/r\le c$, then for an independent copy $U'$,
--
--   $$1+\chi^2(\mathbb E\operatorname{Poi}(nU),\operatorname{Poi}(nr))=\mathbb E\exp\!\left(\frac{n(U-r)(U'-r)}r\right),\qquad \chi^2\le C_c n^2v^2/r^2.$$
--
--   For any finite nonnegative vectors $r,q$,
--
--   $$\sum_i(\sqrt{r_i}-\sqrt{q_i})^2\le\sum_iT_{q_i}(r_i).$$
--
--   The statement also asserts that every finite-vector Poisson mixture of a probability prior is a probability measure, ensuring that measure total variation is used with its probability meaning. These comparisons are the scalar observation-law interface for the lower bounds.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: χ² and expectation of the nonnegative exponential → extended nonnegative singleton sums and an iterated nonnegative integral; reason: divergence infinity cannot disappear as a real tsum or nonintegrable integral default
--   - encoding: Poisson mixtures of laws → singleton masses are integrated and summed into a measure, with probability normalization asserted; reason: avoids a nonmeasurable bind default; on nonnegative intensities it is the same mixture
--   - encoding: C_c in the bounded-exponent estimate → C is chosen after c and before every instance; reason: the only permitted dependence of this constant is on c
--   - generalization: mean-to-reference comparison for a probability reference q → display (11) for arbitrary finite nonnegative vectors r and q; reason: the inequality is coordinatewise and needs no mass normalization; all source mean and reference vectors are included
--   - generalization: Poisson observation mixtures at nonnegative rates of nonnegative scalar or probability-vector laws → the auxiliary mixture-normalization conjunct permits any real n and any probability prior on real vectors; reason: Real.toNNReal clips every coordinate rate to a valid nonnegative rate; source instances have nonnegative rates so clipping changes none of them
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.6, §5, displays (9)–(11), continuing on p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace IdentityTesting39.ExactRadius

/-- §5, (9)–(11), printed pp.6–7 / PDF pp.7–8. -/
theorem eq_9_10_11_poisson :
    (∀ (μ : Measure ℝ) (n : ℝ), NonnegativeSecondMomentLaw μ → 0 ≤ n →
      IsProbabilityMeasure (scalarPoissonMixture n μ) ∧
      MarkovChainCLT.tvDist (scalarPoissonMixture n μ)
        (poissonMeasure (Real.toNNReal (n*scalarMean μ))) ≤ n^2*scalarVariance μ) ∧
    (∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure ℝ) (n R : ℝ), NonnegativeSecondMomentLaw μ →
        0 < n → 0 < scalarMean μ → 0 ≤ R →
        (∀ᵐ u ∂μ, |u-scalarMean μ| ≤ R) → n*R^2/scalarMean μ ≤ c →
        1 + chiSquare (scalarPoissonMixture n μ)
          (poissonMeasure (Real.toNNReal (n*scalarMean μ))) =
            ∫⁻ u, ∫⁻ u', ENNReal.ofReal (Real.exp
              (n*(u-scalarMean μ)*(u'-scalarMean μ)/scalarMean μ)) ∂μ ∂μ ∧
        chiSquare (scalarPoissonMixture n μ)
          (poissonMeasure (Real.toNNReal (n*scalarMean μ))) ≤
            ENNReal.ofReal (C*n^2*(scalarVariance μ)^2/(scalarMean μ)^2)) ∧
    (∀ (ι : Type) [Fintype ι] (r q : ι → ℝ), (∀ i, 0 ≤ r i) → (∀ i, 0 ≤ q i) →
      (∑ i, (Real.sqrt (r i)-Real.sqrt (q i))^2) ≤ ∑ i, triangularCost (q i) (r i)) ∧
    (∀ (ι : Type) [Fintype ι] (n : ℝ) (π : Measure (ι → ℝ)),
      IsProbabilityMeasure π → IsProbabilityMeasure (poissonMixture n π)) := by sorry

end IdentityTesting39.ExactRadius
