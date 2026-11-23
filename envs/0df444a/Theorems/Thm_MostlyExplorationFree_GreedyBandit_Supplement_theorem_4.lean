-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_Supplement_theorem_4
-- name    : MostlyExplorationFree.GreedyBandit.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:57:56.5969+00:00
-- url     : https://prove2.me/theorems/0a180301-3f62-4ed4-8dae-fb734c4eb079
-- title:
--   Theorem 4 (corrected: gamma domain and noise convention) — purely greedy success of Greedy-First
-- statement:
--   Under the independent model and Assumptions 1, 2 and 4, suppose $K\ge2$, $d,m\ge1$, $K_{\rm sub}=\varnothing$, $\sigma,\lambda_0>0$ and $q\ge1$. Run Greedy-First with $m$ forced samples per arm, arbitrary independent initial estimates, and switch inputs $(\lambda_0,t_0)$. For every
--   $$0<\gamma<1,\quad\gamma\le1-\frac{\lambda_0}{4\lambda_1},\quad\delta>0,\quad Km+1\le p\le t_0,$$
--   the specific event $E=\mathrm{Success}\cap\mathrm{NoSwitch}$ satisfies
--   $$\mathbb P(E)\ge1-L'(\gamma,\delta,p),\qquad L'=L+\frac{(K-1)d\exp[-D_1(\gamma)p]}{1-\exp[-D_1(\gamma)]}.$$
--   Furthermore there is a constant $C$ independent of $T$ such that
--   $$\mathbb E\left[\mathbb I_E\sum_{t=1}^T\rho_t^{\rm GF}\right]\le C\log T\qquad(T\ge2).$$
--   Here Success is the all-arm accuracy event from Theorem 2, and NoSwitch requires every covariance test after $t_0$ to pass. The input $\lambda_0$ is not assumed to be a covariate-diversity constant.
--
--   This companion theorem guarantees purely greedy operation with logarithmic regret. It needs no bound on the fallback's regret, since the two runs coincide on NoSwitch.
--
--   Differences from the source:
--   - generalization: The context distribution is described by a Lebesgue density. → The context law is an arbitrary probability measure.; reason: The results use only the law, and the paper itself includes discrete Rademacher examples on pp. 9–11.
--   - correction: Definition 1 gives the MGF bound only at positive arguments and allows zero noise scale. → The noise has a two-sided subgaussian MGF bound and the variance proxy scale is positive.; reason: The estimation arguments require mean-zero two-sided tails; the displayed bounds divide by the squared scale. The noiseless case is excluded rather than assigned Lean division-by-zero values.
--   - encoding: The paper uses arms 1 through K, Euclidean vectors and time from 1. → Arms are Fin K, vectors use the published l2norm, and every permitted model has d at least 1 and K at least 2; time differences in formulas are real.; reason: This preserves the source domain and avoids an empty Rayleigh sphere, empty arm maxima and truncated subtraction.
--   - correction: Display (11) omits the lower and upper strict restrictions on gamma. → Its parameter domain includes 0 < gamma < 1 as well as the printed upper constraint.; reason: Theorem 2 and Lemma 17 require this domain. Negative gamma can give a positive success bound even when lambda0 exceeds 4 xmax squared and switching is certain; excluded gamma values are at most zero or at least one.
--   - reading: The lower bound optimizes over admissible triples, which can form an empty set. → The bound is asserted for every admissible triple, and the event is Success intersected with NoSwitch.; reason: This matches the proof on pp. 58–59 and imposes no false probability-one assertion when the parameter set is empty.
--   - reading: The statement says purely greedy and logarithmic cumulative regret on the successful event. → The event enforces no switch and has one indicator-weighted expected regret coefficient for every T at least 2.; reason: This is the regret notion specified on p. 7 applied to the event constructed on p. 58.
--   - generalization: Assumption 4 requires each suboptimal arm to lose by more than h at every x in the context support 𝒳. → The suboptimal-arm condition is required only for μ-almost every x.; reason: Every use of the condition is through a context X_t with law μ, so a μ-null exception set changes no probability; the almost-sure condition is implied by the pointwise one on the support.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 25, Theorem 4 (governing context pp. 7–8, 19–25 and Appendix F pp. 53–59)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory

theorem theorem_4
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d K : ℕ} [NeZero K]
    (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K)
    (σ xmax h : ℝ) (m : ℕ) (hd : 1 ≤ d) (hK : 2 ≤ K) (hm : 1 ≤ m)
    (hσ : 0 < σ)
    (hmodel : IsModel P μ E σ)
    (bmax C0 lam1 lam0 : ℝ) (t0 q : ℕ) (hlam0 : 0 < lam0) (hq : 1 ≤ q)
    (hparams : ParameterSet μ E.β xmax bmax)
    (hmargin : BastaniBayati.LassoBandit.MarginCondition μ E.β C0)
    (hpd : PositiveDefiniteness μ E.β ∅ h lam1) :
    (∀ γ δ : ℝ, 0 < γ → γ < 1 → γ ≤ 1 - lam0 / (4 * lam1) → 0 < δ →
      ∀ p : ℕ, K * m + 1 ≤ p → p ≤ t0 →
        1 - Lprime P E m ∅ σ xmax h lam1 γ δ p ≤
          P.real (Success E m h xmax ∩ NoSwitch E m lam0 t0)) ∧
    LogarithmicOn P E (firstArm E m lam0 t0 q h)
      (Success E m h xmax ∩ NoSwitch E m lam0 t0) := by sorry

end MostlyExplorationFree.GreedyBandit.Supplement
