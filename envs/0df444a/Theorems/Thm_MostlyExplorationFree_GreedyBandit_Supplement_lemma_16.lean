-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_Supplement_lemma_16
-- name    : MostlyExplorationFree.GreedyBandit.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:54:41.000594+00:00
-- url     : https://prove2.me/theorems/bc1d31a5-a5b2-46b3-a3a4-302ec00b2dab
-- title:
--   Lemma 16 (corrected: J threshold and two-sided noise) — late OLS error
-- statement:
--   Assume the independent model and Assumptions 1 and 4, with $K\ge2$, $d,m\ge1$, $\sigma>0$, $0<\gamma<1$ and $t\ge p\ge Km+1$. For every arm $i$, including suboptimal arms,
--   $$\mathbb P[\overline G_{i,t}^{\theta_1}\cap J_{i,t}^{\lambda_1(1-\gamma)}]\le2d\exp[-D_2(\gamma)(t-m|K_{\rm sub}|)],$$
--   where $\theta_1=h/(2x_{\max})$ and $D_2(\gamma)=\lambda_1^2h^2(1-\gamma)^2/(8d\sigma^2x_{\max}^4)$.
--
--   This bounds estimation failure jointly with a sufficiently large covariance matrix and supplies the late-time estimation term for Theorems 2 and 4.
--
--   Differences from the source:
--   - generalization: The context distribution is described by a Lebesgue density. → The context law is an arbitrary probability measure.; reason: The results use only the law, and the paper itself includes discrete Rademacher examples on pp. 9–11.
--   - correction: Definition 1 gives the MGF bound only at positive arguments and allows zero noise scale. → The noise has a two-sided subgaussian MGF bound and the variance proxy scale is positive.; reason: The estimation arguments require mean-zero two-sided tails; the displayed bounds divide by the squared scale. The noiseless case is excluded rather than assigned Lean division-by-zero values.
--   - encoding: The paper uses arms 1 through K, Euclidean vectors and time from 1. → Arms are Fin K, vectors use the published l2norm, and every permitted model has d at least 1 and K at least 2; time differences in formulas are real.; reason: This preserves the source domain and avoids an empty Rayleigh sphere, empty arm maxima and truncated subtraction.
--   - generalization: The greedy algorithm starts at zero, and Greedy-First starts at random. → The supporting lemmas allow any jointly distributed initial estimates independent of all primitive observations and tie variables.; reason: On a positive-Gram event the estimate is OLS; the other arguments need only accuracy of the resulting estimates. Both algorithms are covered.
--   - correction: The display defining J on p. 53 prints λt − m|K_sub|. → The threshold is λ(t − m|K_sub|).; reason: The explicit step 3 on p. 20 and the Chernoff application on p. 55 both put the entire effective sample size inside the product.
--   - generalization: Assumption 4 requires each suboptimal arm to lose by more than h at every x in the context support 𝒳. → The suboptimal-arm condition is required only for μ-almost every x.; reason: Every use of the condition is through a context X_t with law μ, so a μ-null exception set changes no probability; the almost-sure condition is implied by the pointwise one on the support.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 56, Lemma 16 (governing context pp. 7–8, 19–25 and Appendix F pp. 53–59)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory

theorem lemma_16
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d K : ℕ} [NeZero K]
    (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K)
    (σ xmax h : ℝ) (m : ℕ) (hd : 1 ≤ d) (hK : 2 ≤ K) (hm : 1 ≤ m)
    (hσ : 0 < σ)
    (hmodel : IsModel P μ E σ)
    (bmax lam1 : ℝ) (Ksub : Finset (Fin K))
    (hparams : ParameterSet μ E.β xmax bmax)
    (hpd : PositiveDefiniteness μ E.β Ksub h lam1)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) (p t : ℕ) (hp : K * m + 1 ≤ p)
    (ht : p ≤ t) (i : Fin K) :
    P.real ((G E m (theta1 h xmax) i t)ᶜ ∩ J E m Ksub (lam1 * (1 - γ)) i t) ≤
      2 * d * Real.exp (-D2 d σ xmax h lam1 γ *
        ((t : ℝ) - (m : ℝ) * Ksub.card)) := by sorry

end MostlyExplorationFree.GreedyBandit.Supplement
