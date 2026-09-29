-- Prove2me | Theorems.Thm_MarkovMixing_distinguishing_statistic_of_pos_variance
-- name    : MarkovMixing.distinguishing_statistic_of_pos_variance
-- status  : Proved
-- author  : @chenmin
-- created : 2026-08-22T16:32:04.723211+00:00
-- url     : https://prove2.me/theorems/61256bd8-16f9-4172-935c-c97cb96fa518
-- title:
--   Proposition 7.8, corrected: distinguishing statistics, with $\sigma^2>0$
-- statement:
--   Let $\mu$ and $\nu$ be probability distributions on a finite set $V$, and let $f : V \to \mathbb{R}$ be a statistic. Write
--   $$\mathbb E_\mu(f) = \sum_{x} f(x)\mu(x), \qquad \operatorname{Var}_\mu(f) = \sum_x \bigl[f(x)-\mathbb E_\mu(f)\bigr]^2 \mu(x),$$
--   and set
--   $$\sigma^2 := \frac{\operatorname{Var}_\mu(f) + \operatorname{Var}_\nu(f)}{2}.$$
--
--   **Claim.** Assume $\sigma^2 > 0$, let $r \ge 0$, and suppose $f$ separates the two means by $r$ standard deviations,
--   $$r\,\sigma \;\le\; \bigl|\mathbb E_\mu(f) - \mathbb E_\nu(f)\bigr| .$$
--   Then the two distributions are far apart in total variation:
--   $$\|\mu - \nu\|_{TV} \;\ge\; 1 - \frac{4}{4+r^2} \;=\; \frac{r^2}{4+r^2}.$$
--
--   This is Proposition 7.8 of Levin--Peres--Wilmer with the hypothesis $\sigma^2 > 0$ made explicit. That hypothesis is not cosmetic: if both variances vanish **and** the means agree — for instance $\mu = \nu$ with $f$ constant — the separation assumption degenerates to $0 \le 0$ and holds for every $r$, while $\|\mu-\nu\|_{TV} = 0$, so the conclusion fails for every $r > 0$. The published proof divides by $\sigma^2 + M^2$, where $M = \tfrac12|\mathbb E_\mu(f)-\mathbb E_\nu(f)|$, which is exactly the step that requires it.
--
--   The bound is the standard tool for turning a *distinguishing statistic* into a mixing-time lower bound: a statistic whose mean shifts by many standard deviations between $P^t(x,\cdot)$ and $\pi$ certifies that the chain has not yet mixed at time $t$. It is stronger than the bound $1 - 8/r^2$ obtained directly from Chebyshev's inequality.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.3, Proposition 7.8 (eq. 7.18-7.19), pp. 92-94, with the hypothesis sigma^2 > 0 added (the published statement is false when both variances and the mean gap vanish; the proof divides by sigma^2 + M^2)

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MarkovMixing

/-- **Proposition 7.8** (LPW), corrected: if a statistic `f` separates the
means of `μ` and `ν` by `r` standard deviations, in the sense that
`|E_μ(f) − E_ν(f)| ≥ r σ` with `σ² = [Var_μ(f) + Var_ν(f)]/2`, **and the
variances do not both vanish**, then `‖μ − ν‖_TV ≥ 1 − 4/(4 + r²)`.  The
positivity hypothesis is necessary: without it, `μ = ν` together with a
constant `f` satisfies the assumption vacuously for every `r`. -/
theorem distinguishing_statistic_of_pos_variance {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (f : V → ℝ)
    (hvar : 0 < distVar μ f + distVar ν f)
    (r : ℝ) (hr : 0 ≤ r)
    (h : r * Real.sqrt ((distVar μ f + distVar ν f) / 2) ≤
      |distExp μ f - distExp ν f|) :
    1 - 4 / (4 + r ^ 2) ≤ tvDist μ ν := by
  sorry

end MarkovMixing
