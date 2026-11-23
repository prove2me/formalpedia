-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_Supplement_theorem_3
-- name    : MostlyExplorationFree.GreedyBandit.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:56:31.564167+00:00
-- url     : https://prove2.me/theorems/59ec3a6b-1b59-4578-9166-53bcc122da86
-- title:
--   Theorem 3 (corrected: horizons, noise and fallback coefficient) — regret, no switching, and vanishing failure
-- statement:
--   This item contains all three conclusions for Algorithm 3 with no forced initial samples and arbitrary independent random initial estimates.
--
--   1. Under the independent model and Assumptions 1, 2 and 4, with $K,d\ge2$, $\sigma,\lambda_0>0$, $q\ge1$, and any real coefficient $C_{\rm OB}$ satisfying the defined fresh Algorithm 4 bound $R_{\rm OB}^{(r)}(n)\le C_{\rm OB}\log n$ for every deterministic absolute restart $r\ge0$ and every $n\ge2$, every $T\ge3$ satisfies
--   $$R_T^{\rm GF}\le[(K-1)C_{\rm GB}+C_{\rm OB}]\log T+2t_0x_{\max}b_{\max}.$$
--   Here $C_{\rm GB}=A+(A+B)/\log3$ is computed from the published form of Theorem 1, with $A$ its logarithmic coefficient and $B=160b_{\max}x_{\max}^3d/\lambda_0+2x_{\max}b_{\max}$. The input $\lambda_0$ is arbitrary in this clause.
--   2. Independently, for $K=2$, $d\ge1$, the independent model, Assumption 1 and covariate diversity with this same $\lambda_0$, the infinite-horizon event of never switching satisfies, for every $t_0\ge0$,
--   $$\mathbb P(\mathrm{NoSwitch})\ge1-\delta(t_0),\qquad\delta(t_0)=\frac{2d\exp[-t_0C_1]}{C_1},\quad C_1=\frac{\lambda_0}{40x_{\max}^2}.$$
--   3. Under the hypotheses of clause 2,
--   $$\lim_{t_0\to\infty}\delta(t_0)=0.$$
--
--   Here $R_{\rm OB}^{(r)}$ uses the same observation sequences shifted by $r$, with a fresh local clock and empty data. The regret clause requires one coefficient valid at every such start; it does not assume that the time-dependent noise laws are identical. The no-switch clause needs no margin condition, positive-definiteness assumption or fallback regret hypothesis.
--
--   Differences from the source:
--   - generalization: The context distribution is described by a Lebesgue density. → The context law is an arbitrary probability measure.; reason: The results use only the law, and the paper itself includes discrete Rademacher examples on pp. 9–11.
--   - correction: Definition 1 gives the MGF bound only at positive arguments and allows zero noise scale. → The noise has a two-sided subgaussian MGF bound and the variance proxy scale is positive.; reason: The estimation arguments require mean-zero two-sided tails; the displayed bounds divide by the squared scale. The noiseless case is excluded rather than assigned Lean division-by-zero values.
--   - encoding: The paper uses arms 1 through K, Euclidean vectors and time from 1. → Arms are Fin K, vectors use the published l2norm, and every permitted model has d at least 1 and K at least 2; time differences in formulas are real.; reason: This preserves the source domain and avoids an empty Rayleigh sphere, empty arm maxima and truncated subtraction.
--   - correction: Theorem 3 does not print a horizon or dimension restriction. → The regret clause has T at least 3 and d at least 2.; reason: Its C_GB is inherited from Theorem 1, which has these ranges; log 1 is zero and Cbar divides by log d. Cases T below 3 and d below 2 are excluded only from the regret clause.
--   - reading: Theorem 1 names C_GB only through its logarithmic upper bound, and Theorem 3 calls C_OB the OLS coefficient. → C_GB is A+(A+B)/log 3 from the published proved form; C_OB bounds the defined fresh OLS run at every absolute start for every n at least 2.; reason: The additive terms in Theorem 1 remain present; p. 24 uses a fresh fallback run, and its coefficient must be uniform over start times. The unsatisfiable n=1 bound is not required.
--   - reading: Algorithm 3 prints an inverse update and executes OLS after the first failed test. → Singular matrices retain the random initial estimate; round R is greedy and R+1 restarts OLS with empty data and local clock 1.; reason: The singular rule is Algorithm 1 on p. 11; the restart is required by the fresh-run bound on p. 24.
--   - generalization: The theorem is presented under standing margin and positive-definiteness assumptions. → The no-switch and limiting clauses assume only the model, Assumption 1 and covariate diversity.; reason: The p. 24 argument uses only the covariance tail bound in these clauses.
--   - correction: The brief reads C_OB as any coefficient for the original fresh OLS run starting at time 1. → One coefficient must bound the defined fresh OLS run at every deterministic absolute restart time, for all n at least 2.; reason: The noises need not be identically distributed. DISPROOF.md gives a full-density bounded-context model with an unshifted coefficient 1/log 2 but Greedy-First regret above 124.6 when that reading predicts below 27.9. The fresh-run step on p. 24 requires restart uniformity; coefficients valid only at the original start are excluded.
--   - generalization: Assumption 4 requires each suboptimal arm to lose by more than h at every x in the context support 𝒳. → The suboptimal-arm condition is required only for μ-almost every x.; reason: Every use of the condition is through a context X_t with law μ, so a μ-null exception set changes no probability; the almost-sure condition is implied by the pointwise one on the support.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 23, Theorem 3 (governing context pp. 7–8, 19–25 and Appendix F pp. 53–59)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Events

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory

theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    (∀ {d K : ℕ} [NeZero K] (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K)
      (σ xmax bmax C0 h lam1 lam0 COB : ℝ) (Ksub : Finset (Fin K)) (t0 q : ℕ),
      2 ≤ d → 2 ≤ K → 0 < σ → 0 < lam0 → 1 ≤ q →
      IsModel P μ E σ → ParameterSet μ E.β xmax bmax → BastaniBayati.LassoBandit.MarginCondition μ E.β C0 →
      PositiveDefiniteness μ E.β Ksub h lam1 → UniformOLSCoefficient P E q h COB →
      ∀ T : ℕ, 3 ≤ T →
        regretOn P E (firstArm E 0 lam0 t0 q h) Set.univ T ≤
          (((K : ℝ) - 1) * CGB d C0 xmax bmax σ lam0 + COB) * Real.log T +
            2 * t0 * xmax * bmax) ∧
    (∀ {d : ℕ} (μ : Measure (Fin d → ℝ)) (E : Environment Ω d 2)
      (σ xmax bmax lam0 : ℝ), 1 ≤ d → 0 < σ →
      IsModel P μ E σ → ParameterSet μ E.β xmax bmax → CovariateDiversity μ lam0 →
      (∀ t0 : ℕ, 1 - switchFailure d lam0 xmax t0 ≤ P.real (NoSwitch E 0 lam0 t0)) ∧
      Filter.Tendsto (switchFailure d lam0 xmax) Filter.atTop (nhds 0)) := by sorry

end MostlyExplorationFree.GreedyBandit.Supplement
