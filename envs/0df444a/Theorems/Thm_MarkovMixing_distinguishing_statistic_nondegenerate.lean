-- Prove2me | Theorems.Thm_MarkovMixing_distinguishing_statistic_nondegenerate
-- name    : MarkovMixing.distinguishing_statistic_nondegenerate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:51:32.278983+00:00
-- url     : https://prove2.me/theorems/d11d3e0c-1d5f-41a5-aaa7-17eeeb4b4272
-- title:
--   Proposition 7.8 -- the distinguishing statistic bound
-- statement:
--   Let $\mu$ and $\nu$ be two probability distributions on a finite set $V$, and let $f:V\to\mathbb R$ be any real-valued **statistic**. Write $E_\mu(f)=\sum_x f(x)\mu(x)$ and $\operatorname{Var}_\mu(f)=E_\mu(f^2)-E_\mu(f)^2$ for the mean and variance of $f$ under $\mu$, and likewise for $\nu$, and set
--   $$\sigma^2=\frac{\operatorname{Var}_\mu(f)+\operatorname{Var}_\nu(f)}{2},$$
--   the average of the two variances. Assume the statistic actually tells the two distributions apart in the mean: $E_\mu(f)\ne E_\nu(f)$. The **total variation distance** is $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$, the largest discrepancy the two distributions assign to any event.
--
--   **The theorem** (Levin–Peres–Wilmer, Proposition 7.8) asserts: if the statistic separates the two means by at least $r\ge0$ standard deviations,
--   $$|E_\mu(f)-E_\nu(f)|\;\ge\;r\,\sigma,$$
--   then the distributions themselves are far apart:
--   $$\|\mu-\nu\|_{TV}\;\ge\;1-\frac{4}{4+r^2}.$$
--
--   This is the standard route to a mixing-time lower bound. To show a chain is far from stationarity at time $t$, one need not analyze the whole distribution: it is enough to find a single statistic whose mean shifts by many standard deviations between $P^t(x,\cdot)$ and $\pi$. The bound is scale-free — only the ratio "mean gap over standard deviation" matters — and it improves with $r$, approaching $1$ as $r\to\infty$; a separation of $r$ standard deviations already forces the two distributions to disagree on some event with probability at least $1-4/(4+r^2)$.
--
--   *A note on the hypothesis $E_\mu(f)\ne E_\nu(f)$.* It does not appear in the proposition as printed, but it is exactly what the proof assumes: the argument opens by assuming the two means are distinct and concludes through $\|\mu-\nu\|_{TV}\ge1-\sigma^2/(\sigma^2+M^2)$, where $M=|E_\mu(f)-E_\nu(f)|/2$. Without a non-degeneracy assumption the statement is false as written: if $f$ has zero variance under both distributions *and* the two means agree, then the hypothesis reads $r\cdot0\le0$ and holds for **every** $r$, while the conclusion demands a positive lower bound on a total variation distance that may be $0$ — take $\mu=\nu$ the point mass on a one-point space, $f=0$ and $r=5$. Distinct means also keep $\sigma^2+M^2$ strictly positive, which is what the final step of the proof divides by. Nothing is lost in applications: a statistic with equal means separates nothing, and the bound it would give at the only admissible $r$ is the vacuous $0\le\|\mu-\nu\|_{TV}$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.3, Proposition 7.8, Eqs. (7.18)-(7.19), p. 92

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MarkovMixing

/-- **Proposition 7.8** (LPW): if a statistic `f` separates the means of `μ`
and `ν` by `r` standard deviations, in the sense that
`|E_μ(f) − E_ν(f)| ≥ r σ` with `σ² = [Var_μ(f) + Var_ν(f)]/2`, then
`‖μ − ν‖_TV ≥ 1 − 4/(4 + r²)`.

The hypothesis that the two means differ does not appear in LPW's printed
statement, but their proof assumes it: it opens with "assume that
`m_α > m_β`" and concludes through `‖α − β‖_TV ≥ 1 − σ²/(σ² + M²)`, where
`M = |E_μ(f) − E_ν(f)|/2`.  Without a non-degeneracy assumption the
proposition as printed is false — when `f` has zero variance under both
distributions *and* the two means agree, `(7.18)` reads `r · 0 ≤ 0` and holds
for every `r`, while the conclusion demands a positive lower bound on a total
variation distance that can be `0` (take `μ` and `ν` both the point mass on a
one-point space, `f = 0`, `r = 5`).  Requiring `E_μ(f) ≠ E_ν(f)` is exactly
the proof's own assumption, and it also keeps `σ² + M²` positive. -/
theorem distinguishing_statistic_nondegenerate {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (f : V → ℝ)
    (hmean : distExp μ f ≠ distExp ν f)
    (r : ℝ) (hr : 0 ≤ r)
    (h : r * Real.sqrt ((distVar μ f + distVar ν f) / 2) ≤
      |distExp μ f - distExp ν f|) :
    1 - 4 / (4 + r ^ 2) ≤ tvDist μ ν := by
  sorry

end MarkovMixing
