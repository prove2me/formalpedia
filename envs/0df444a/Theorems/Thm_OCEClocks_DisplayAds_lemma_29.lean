-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_29
-- name    : OCEClocks.DisplayAds.lemma_29
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:22:53.825257+00:00
-- url     : https://prove2.me/theorems/aba0c218-feab-4639-8dcb-42b7fd150140
-- title:
--   Lemma 29 — the winning probability $D_x$ given the first age
-- statement:
--   Let $\lambda>0$ and $0<x<1$. For a request of mass $x$ handled by the First-Age Poisson generator, let $D_x(a)$ be the probability that it wins against a fresh competing clock of rate $1-x$, conditional on its interval having first age $a$. Its clock is $Y=-\log U/x$ with $U$ from (3). Then
--
--   $$D_x(a)=\begin{cases}c_x:=x\,e^{-\lambda(1-x)}, & a=0,\\[2pt] F_x(a)^{(1-x)/x}, & a>0.\end{cases}\qquad(30)$$
--
--   In particular, $D_x$ is nondecreasing in $a\ge0$, with minimum $D_x(0)=c_x$.
--
--   $D_x$ enters the explicit kernel formula of Lemma 32 and the monotonicity arguments behind Lemmas 16 and 17.
--
--   **Formalization Note** $D_x(a)$ is `winProbGivenAge λ x a`, the average over $V\sim\mathrm{Unif}[0,1]$ of $\Pr[Y<Z]$ for $Z\sim\mathrm{Exp}(1-x)$. The "minimum" clause is stated as $D_x(0)\le D_x(a)$ for every $a\ge0$, next to `MonotoneOn` on $[0,\infty)$.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 37, Lemma 29, eq. (30)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Kernels

namespace OCEClocks.DisplayAds

/-- Lemma 29 (p. 37), eq. (30): the winning probability `D_x` given the first age, for a request
`0 < x < 1`; `D_x` is nondecreasing on ages with minimum `D_x(0) = c_x = x e^{-λ(1-x)}`. -/
theorem lemma_29 (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    winProbGivenAge lam x 0 = x * Real.exp (-(lam * (1 - x))) ∧
    (∀ a : ℝ, 0 < a → winProbGivenAge lam x a = firstAgeCDF lam x a ^ ((1 - x) / x)) ∧
    MonotoneOn (winProbGivenAge lam x) (Set.Ici 0) ∧
    (∀ a : ℝ, 0 ≤ a → winProbGivenAge lam x 0 ≤ winProbGivenAge lam x a) := by sorry

end OCEClocks.DisplayAds
