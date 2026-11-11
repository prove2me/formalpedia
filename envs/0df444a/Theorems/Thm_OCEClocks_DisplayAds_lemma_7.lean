-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_7
-- name    : OCEClocks.DisplayAds.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:21:23.955033+00:00
-- url     : https://prove2.me/theorems/3fe0b396-385a-40a5-bffa-b6e72fbe5586
-- title:
--   Lemma 7 — closed form of the first-age distribution function $F_x$
-- statement:
--   Let $\lambda>0$ and consider the stationary Poisson process of rate $\lambda$ on $\mathbb R$. For an interval $I$, the first age $\widehat A(I)$ is the age (time since the previous arrival) of the first arrival in $I$, or $0$ if $I$ has no arrival. $F_x$ is the distribution function of the first age of an interval of length $x$. Then for every $x>0$ and $a\ge0$,
--
--   $$F_x(a)=\begin{cases}1+e^{-\lambda x}-(1+\lambda a)e^{-\lambda a}, & 0\le a<x,\\[2pt] 1-\lambda x\,e^{-\lambda a}, & x\le a.\end{cases}\qquad(2)$$
--
--   $F_x$ has an atom $e^{-\lambda x}$ at $0$ (empty intervals) and is continuous elsewhere. This is what lets the First-Age Poisson generator turn first ages into exponential clocks by a randomized probability integral transform.
--
--   **Formalization Note** The two cases are stated as two implications for every $x>0$ and $a\ge0$.
--
--   Differences from the source:
--   - encoding: F_x is the distribution function of the first age of any interval of length x → F_x(a) = P[Â([0, x)) ≤ a] for the process built from i.i.d. Exp(λ) gaps as on p. 8; reason: by stationarity (p. 7) the law depends only on the length; the construction is the paper's own
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 7, Lemma 7, eq. (2) (proof p. 37, Appendix A)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_PoissonProcess

namespace OCEClocks.DisplayAds

/-- Lemma 7 (p. 7): the closed form (2) of the first-age distribution function `F_x`. -/
theorem lemma_7 (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (hx : 0 < x) (a : ℝ) (ha : 0 ≤ a) :
    (a < x → firstAgeCDF lam x a =
        1 + Real.exp (-(lam * x)) - (1 + lam * a) * Real.exp (-(lam * a))) ∧
    (x ≤ a → firstAgeCDF lam x a = 1 - lam * x * Real.exp (-(lam * a))) := by sorry

end OCEClocks.DisplayAds
