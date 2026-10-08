-- Prove2me | Theorems.Thm_KendallBD_MinVar_min_fluctuation
-- name    : KendallBD.MinVar.min_fluctuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:26.468989+00:00
-- url     : https://prove2.me/theorems/3a9360fd-bb6f-443b-945f-e18a1fbe9714
-- title:
--   §6, (56), p. 12 — unique minimum-fluctuation rates for a prescribed mean
-- statement:
--   Let $\bar n$ be a positive $C^1$ mean curve with $\bar n_0=1$ and write $g(t)=\bar n_t'/\bar n_t$. Set $\lambda_*(t)=\max\{g(t),0\}$ and $\mu_*(t)=\max\{-g(t),0\}$. Then:
--
--   1. These are continuous nonnegative rates that give the mean $\bar n$.
--   2. For every other continuous nonnegative rate pair $\lambda,\mu$ with the same mean and every $t\ge0$,
--
--      $$V_{\lambda_*,\mu_*}(t)\le V_{\lambda,\mu}(t).$$
--
--   3. If equality holds for every $t\ge0$, then $\lambda(t)=\lambda_*(t)$ and $\mu(t)=\mu_*(t)$ for every $t\ge0$.
--
--   Thus the pair simultaneously minimizes the variance throughout the entire time course and is the unique pair doing so. On a decreasing, increasing or constant interval of $\bar n$, this is precisely the respective case of (56).
--
--   **Formalization Note** The positive-and-negative-part formula applies to every positive $C^1$ mean, extending Kendall's presentation, which assumes a partition into monotonicity intervals. Strict positivity on all real times makes the candidate rates continuous; the conclusions concern nonnegative time only. The variance is represented by (14c), rather than by a separately constructed probability law.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §6, (56) and preceding paragraph, p. 12; variance (14c), p. 4

import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- Kendall (1948), (56), p. 12: the unique rate pair minimizing variance
simultaneously at all nonnegative times for a prescribed mean. -/
theorem min_fluctuation (nbar : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1) :
    (Admissible (lamStar nbar) (muStar nbar) ∧
      HasMean (lamStar nbar) (muStar nbar) nbar) ∧
    (∀ lam mu : ℝ → ℝ, Admissible lam mu → HasMean lam mu nbar →
      ∀ t : ℝ, 0 ≤ t →
        fluct (lamStar nbar) (muStar nbar) t ≤ fluct lam mu t) ∧
    (∀ lam mu : ℝ → ℝ, Admissible lam mu → HasMean lam mu nbar →
      (∀ t : ℝ, 0 ≤ t →
        fluct lam mu t = fluct (lamStar nbar) (muStar nbar) t) →
      ∀ t : ℝ, 0 ≤ t →
        lam t = lamStar nbar t ∧ mu t = muStar nbar t) := by sorry

end KendallBD.MinVar
