-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_Supplement_lemma_14
-- name    : MostlyExplorationFree.GreedyBandit.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:51:50.986837+00:00
-- url     : https://prove2.me/theorems/3e58eaf9-e0a9-4222-bc2b-931392cb62ab
-- title:
--   Lemma 14 (corrected: two-sided noise) — early adaptive OLS error
-- statement:
--   Use the independent model, Assumption 1, $K\ge2$, $d,m\ge1$, and positive $\sigma,h,\delta$. For integers $Km+1\le t<p$ and every arm $i$,
--   $$\mathbb P[H_i^\delta\cap\overline G_{i,t}^{\theta_1}]\le2d\exp\!\left(-\frac{\theta_1^2\delta^2}{2d(t-(K-1)m)\sigma^2x_{\max}^2}\right).$$
--   The events and $\theta_1=h/(2x_{\max})$ are defined as in Lemma 13. The integer $p\ge Km+1$ is an arbitrary end of the early interval; the bound applies to every later-than-initialization period by choosing a larger $p$.
--
--   This supplies the finite early-time part of the failure bound used by Theorems 2 and 4. The denominator counts the maximum possible number of samples of one arm after the forced samples assigned to other arms.
--
--   Differences from the source:
--   - generalization: The context distribution is described by a Lebesgue density. → The context law is an arbitrary probability measure.; reason: The results use only the law, and the paper itself includes discrete Rademacher examples on pp. 9–11.
--   - correction: Definition 1 gives the MGF bound only at positive arguments and allows zero noise scale. → The noise has a two-sided subgaussian MGF bound and the variance proxy scale is positive.; reason: The estimation arguments require mean-zero two-sided tails; the displayed bounds divide by the squared scale. The noiseless case is excluded rather than assigned Lean division-by-zero values.
--   - encoding: The paper uses arms 1 through K, Euclidean vectors and time from 1. → Arms are Fin K, vectors use the published l2norm, and every permitted model has d at least 1 and K at least 2; time differences in formulas are real.; reason: This preserves the source domain and avoids an empty Rayleigh sphere, empty arm maxima and truncated subtraction.
--   - generalization: The greedy algorithm starts at zero, and Greedy-First starts at random. → The supporting lemmas allow any jointly distributed initial estimates independent of all primitive observations and tie variables.; reason: On a positive-Gram event the estimate is OLS; the other arguments need only accuracy of the resulting estimates. Both algorithms are covered.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 54, Lemma 14 (governing context pp. 7–8, 19–25 and Appendix F pp. 53–59)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory

theorem lemma_14
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d K : ℕ} [NeZero K]
    (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K)
    (σ xmax h : ℝ) (m : ℕ) (hd : 1 ≤ d) (hK : 2 ≤ K) (hm : 1 ≤ m)
    (hσ : 0 < σ) (hh : 0 < h)
    (hmodel : IsModel P μ E σ)
    (bmax : ℝ) (hparams : ParameterSet μ E.β xmax bmax)
    (δ : ℝ) (hδ : 0 < δ) (p t : ℕ) (hp : K * m + 1 ≤ p)
    (ht : K * m + 1 ≤ t) (htp : t < p) (i : Fin K) :
    P.real (H E m δ i ∩ (G E m (theta1 h xmax) i t)ᶜ) ≤
      2 * d * Real.exp (-(theta1 h xmax) ^ 2 * δ ^ 2 /
        (2 * d * ((t : ℝ) - ((K : ℝ) - 1) * m) * σ ^ 2 * xmax ^ 2)) := by sorry

end MostlyExplorationFree.GreedyBandit.Supplement
