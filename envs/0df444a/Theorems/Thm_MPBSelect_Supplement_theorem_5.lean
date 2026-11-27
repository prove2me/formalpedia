-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_5
-- name    : MPBSelect.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:49:39.816377+00:00
-- url     : https://prove2.me/theorems/cc68b532-9d2a-49a8-89f4-7828bb0c8010
-- title:
--   Theorem 5 — Algorithm 2 converges to the optimal balance system
-- statement:
--   For every complete stochastic run of Algorithm 2, the following hold almost surely:
--
--   1. at every parameter, the global-balance residual tends to zero;
--   2. for every two distinct pairs of $\Xi$, the ratio of their weighted empirical rates tends to one;
--   3. every solution-parameter pair is sampled unboundedly often;
--   4. for every $(i^*,\theta_b)\in\Xi^{\mathrm{adv}}$, $N_{i^*}^n(\theta_b)/n\to0$.
--
--   Thus posterior sampling makes the adversarial MPB counts diverge while keeping their asymptotic ratios at zero.
--
--   Differences from the source:
--   - encoding: Algorithm 2 is specified by pseudocode and posterior draws → a filtered run relation includes the warm start, normal posterior draws, their discard after each iteration, the unchanged outer MPB, the updated inner optima and the full Algorithm 1 decision; reason: this is the same complete adaptive algorithm
--   - encoding: $\limsup_n N_i^n(\theta_b)=\infty$ → for every integer threshold some count reaches it; reason: for natural-valued counts these are equivalent statements of unbounded sampling
--   - encoding: $G_{i,n}(\theta_b)$, the plug-in $G$ with the sample ratios $\alpha_{\cdot,n}$, the posterior means and $i^b_n$ → `empiricalTrueG`, the same formula with the counts $N^n_\cdot(\theta_b)$ in place of $\alpha_{\cdot,n}(\theta_b)$ and the true $i^b$; reason: counts are $n$ times the ratios, so every ratio of two such rates is unchanged, and almost surely $i^b_n=i^b$ eventually because every count diverges (a conclusion of the theorem), so the limits coincide
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Algorithm 2 and Theorem 5, p.24

import Mathlib
import Definitions.Def_MPBSelect_Supplement_Sequential

open Filter MeasureTheory
open scoped Topology

namespace MPBSelect.Supplement

/-- **Theorem 5 (strong consistency of Algorithm 2's sampling ratios).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 5,
p.24, for the complete posterior-sampling run relation of Algorithm 2.

Almost surely: every global-balance residual tends to zero; every ratio of two distinct weighted
empirical rates on `Ξ` tends to one; every pair is sampled unboundedly often; and the MPB's
sampling fraction tends to zero on `Ξ^adv`. -/
theorem theorem_5 {k B : ℕ} (P : MPBSelect.Problem k B) (D : SequentialData P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (Z : ℕ → Fin B → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (istar : ℕ → Ω → Fin k) (selected decision : ℕ → Ω → Fin k × Fin B)
    (hRun : IsAlgorithm2Run P D μ F Y Z N istar selected decision) :
    ∀ᵐ ω ∂μ,
      (∀ b : Fin B,
        Tendsto (fun t =>
          (allocationFraction D N t ω (P.ib b) b / P.lam (P.ib b) b) ^ 2 -
            ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ P.ib b ∧ j ≠ P.istar),
              (allocationFraction D N t ω j b / P.lam j b) ^ 2)
          atTop (𝓝 0)) ∧
      (∀ x ∈ P.Xi, ∀ x' ∈ P.Xi, x ≠ x' →
        Tendsto (fun t =>
          (P.W x.1 x.2 * empiricalTrueG P D Y N t ω x.1 x.2) /
            (P.W x'.1 x'.2 * empiricalTrueG P D Y N t ω x'.1 x'.2))
          atTop (𝓝 1)) ∧
      (∀ i b, UnboundedSampling N ω i b) ∧
      (∀ b, P.ib b ≠ P.istar →
        Tendsto (fun t => (N t ω P.istar b : ℝ) / (D.total t : ℝ)) atTop (𝓝 0)) := by sorry

end MPBSelect.Supplement
