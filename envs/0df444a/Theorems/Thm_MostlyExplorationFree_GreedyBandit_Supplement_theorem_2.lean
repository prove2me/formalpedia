-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_Supplement_theorem_2
-- name    : MostlyExplorationFree.GreedyBandit.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:55:58.099812+00:00
-- url     : https://prove2.me/theorems/ff6ef719-46c0-4154-8117-223367c755d1
-- title:
--   Theorem 2 (corrected: two-sided noise) — success probability and logarithmic regret of greedy play
-- statement:
--   For the independent $K$-arm model, let Assumptions 1, 2 and 4 hold, with $K\ge2$, $d,m\ge1$ and $\sigma>0$. Start every estimate at zero, give every arm $m$ forced samples, then follow the greedy policy. Let
--   $$\mathrm{Success}=\{\forall i,\ \forall t\ge Km,\ \|\hat\beta(S_{i,t})-\beta_i\|_2<h/(2x_{\max})\}.$$
--   For every $0<\gamma<1$, $\delta>0$ and integer $p\ge Km+1$, using exactly the function $L$ in (9),
--   $$\mathbb P(\mathrm{Success})\ge1-L(\gamma,\delta,p).$$
--   Moreover there is one real constant $C$, independent of $T$, such that
--   $$\mathbb E\left[\mathbb I_{\mathrm{Success}}\sum_{t=1}^T\rho_t\right]\le C\log T\qquad(T\ge2).$$
--   The function $L$ and its constants $D_1,D_2$ are defined in the accompanying event definition, with the good-initial-design probability kept in its initial-error term.
--
--   This is the general-arm companion to the published covariate-diversity theorem. It guarantees logarithmic regret on the particular event constructed in the paper, rather than on an unspecified event.
--
--   Differences from the source:
--   - generalization: The context distribution is described by a Lebesgue density. → The context law is an arbitrary probability measure.; reason: The results use only the law, and the paper itself includes discrete Rademacher examples on pp. 9–11.
--   - correction: Definition 1 gives the MGF bound only at positive arguments and allows zero noise scale. → The noise has a two-sided subgaussian MGF bound and the variance proxy scale is positive.; reason: The estimation arguments require mean-zero two-sided tails; the displayed bounds divide by the squared scale. The noiseless case is excluded rather than assigned Lean division-by-zero values.
--   - encoding: The paper uses arms 1 through K, Euclidean vectors and time from 1. → Arms are Fin K, vectors use the published l2norm, and every permitted model has d at least 1 and K at least 2; time differences in formulas are real.; reason: This preserves the source domain and avoids an empty Rayleigh sphere, empty arm maxima and truncated subtraction.
--   - reading: The success lower bound is 1 minus an infimum of L. → The probability is at least 1 − L for every admissible triple.; reason: This is the equivalent pointwise bound and avoids real-infimum default values.
--   - reading: The statement says logarithmic cumulative regret with a probability guarantee. → The constructed success event has the probability bound, and its indicator-weighted expected pseudo-regret has one coefficient for all T at least 2.; reason: The paper defines regret as an expectation and identifies the success event on pp. 20 and 58; T=1 cannot satisfy a nonzero bound proportional to log 1.
--   - generalization: Assumption 4 requires each suboptimal arm to lose by more than h at every x in the context support 𝒳. → The suboptimal-arm condition is required only for μ-almost every x.; reason: Every use of the condition is through a context X_t with law μ, so a μ-null exception set changes no probability; the almost-sure condition is implied by the pointwise one on the support.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 19, Theorem 2 (governing context pp. 7–8, 19–25 and Appendix F pp. 53–59)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory

theorem theorem_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d K : ℕ} [NeZero K]
    (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K)
    (σ xmax h : ℝ) (m : ℕ) (hd : 1 ≤ d) (hK : 2 ≤ K) (hm : 1 ≤ m)
    (hσ : 0 < σ)
    (hmodel : IsModel P μ E σ)
    (bmax C0 lam1 : ℝ) (Ksub : Finset (Fin K))
    (hparams : ParameterSet μ E.β xmax bmax)
    (hmargin : BastaniBayati.LassoBandit.MarginCondition μ E.β C0)
    (hpd : PositiveDefiniteness μ E.β Ksub h lam1)
    (hinitial : ∀ ω i, E.initial ω i = 0) :
    (∀ γ δ : ℝ, 0 < γ → γ < 1 → 0 < δ → ∀ p : ℕ, K * m + 1 ≤ p →
      1 - L P E m Ksub σ xmax h lam1 γ δ p ≤ P.real (Success E m h xmax)) ∧
    LogarithmicOn P E (arm E m) (Success E m h xmax) := by sorry

end MostlyExplorationFree.GreedyBandit.Supplement
