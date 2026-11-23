-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_Supplement_lemma_13
-- name    : MostlyExplorationFree.GreedyBandit.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:50:35.596849+00:00
-- url     : https://prove2.me/theorems/2b8c2612-6ddf-4426-a39d-1a8e3de468b9
-- title:
--   Lemma 13 (corrected: two-sided noise) — OLS error immediately after initialization
-- statement:
--   Let $K\ge2$, $d,m\ge1$, and let the independent context/noise model hold with $\sigma,x_{\max},h,\delta>0$. For any arm $i$, at the end of the $Km$ forced initialization periods,
--   $$\mathbb P[H_i^\delta\cap\overline G_{i,Km}^{\theta_1}]\le2d\,q_\delta\exp\!\left(-\frac{\theta_1^2\delta}{2d\sigma^2}\right),\qquad\theta_1=\frac{h}{2x_{\max}}.$$
--   Here $q_\delta$ is the probability that $m$ independent contexts give a Gram minimum eigenvalue at least $\delta$, $H_i^\delta$ is the corresponding event for arm $i$'s forced samples, and $G$ is the strict Euclidean estimation-accuracy event.
--
--   This is the initial random-design error bound supporting Theorems 2 and 4; it retains the multiplicative probability of a good Gram matrix. Bounded contexts, a margin condition and positive-definiteness are not needed for this estimate.
--
--   Differences from the source:
--   - generalization: The context distribution is described by a Lebesgue density. → The context law is an arbitrary probability measure.; reason: The results use only the law, and the paper itself includes discrete Rademacher examples on pp. 9–11.
--   - correction: Definition 1 gives the MGF bound only at positive arguments and allows zero noise scale. → The noise has a two-sided subgaussian MGF bound and the variance proxy scale is positive.; reason: The estimation arguments require mean-zero two-sided tails; the displayed bounds divide by the squared scale. The noiseless case is excluded rather than assigned Lean division-by-zero values.
--   - encoding: The paper uses arms 1 through K, Euclidean vectors and time from 1. → Arms are Fin K, vectors use the published l2norm, and every permitted model has d at least 1 and K at least 2; time differences in formulas are real.; reason: This preserves the source domain and avoids an empty Rayleigh sphere, empty arm maxima and truncated subtraction.
--   - generalization: The greedy algorithm starts at zero, and Greedy-First starts at random. → The supporting lemmas allow any jointly distributed initial estimates independent of all primitive observations and tie variables.; reason: On a positive-Gram event the estimate is OLS; the other arguments need only accuracy of the resulting estimates. Both algorithms are covered.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 53, Lemma 13 (governing context pp. 7–8, 19–25 and Appendix F pp. 53–59)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory

theorem lemma_13
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d K : ℕ} [NeZero K]
    (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K)
    (σ xmax h : ℝ) (m : ℕ) (hd : 1 ≤ d) (hK : 2 ≤ K) (hm : 1 ≤ m)
    (hσ : 0 < σ) (hxmax : 0 < xmax) (hh : 0 < h)
    (hmodel : IsModel P μ E σ)
    (δ : ℝ) (hδ : 0 < δ) (i : Fin K) :
    P.real (H E m δ i ∩ (G E m (theta1 h xmax) i (K * m))ᶜ) ≤
      2 * d * sampleGood P E m δ *
        Real.exp (-(theta1 h xmax) ^ 2 * δ / (2 * d * σ ^ 2)) := by sorry

end MostlyExplorationFree.GreedyBandit.Supplement
