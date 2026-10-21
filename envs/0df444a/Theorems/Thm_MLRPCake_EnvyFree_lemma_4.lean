-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_lemma_4
-- name    : MLRPCake.EnvyFree.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:24.030984+00:00
-- url     : https://prove2.me/theorems/8621d064-fc9c-484e-b3e2-1707205eca20
-- title:
--   Lemma 4, p. 13 — BinSearch returns a δ-ripple division in poly(n, log λ, log 1/δ) iterations
-- statement:
--   There is a universal constant $c\in\mathbb N$ such that the following holds. Let $\mathcal C=\langle[n],\{f_i\}_i\rangle$ be a cake-division instance with $n\ge1$ agents whose cut and eval queries are $\lambda$-Lipschitz for some $\lambda\ge1$, and let $\delta\in(0,1)$. Run BinSearch (Algorithm 1) on $\mathcal C$ with parameter $\delta$. Then BinSearch returns. More precisely, there is a first iteration $T$ at which the queried midpoint $m$ satisfies $\mathrm{RD}_n(m)\in[1-\delta,1)$, with
--   $$T\le c\,\big(n+\log_2\lambda+\log_2(1/\delta)+1\big)^{c},$$
--   and the returned points $x_0=0$, $x_1=m$, $x_i=\mathrm{RD}_i(m)$ form a $\delta$-ripple division of $\mathcal C$.
--
--   So a $\delta$-ripple division can be computed in $O(\mathrm{poly}(n,\log\lambda,\log\frac1\delta))$ time in the Robertson–Webb query model. The paper's appendix gives the explicit count $2(n-1)\log(2\lambda/\delta)$ iterations.
--
--   **Formalization Note** "Time" is measured in iterations of BinSearch. Each iteration evaluates $\mathrm{RD}_n$ once, at a cost of $2(n-1)$ Robertson–Webb queries, so the query count is polynomial as well. The polynomial is universal: $c$ is chosen before the instance. No MLRP hypothesis, as on the page. $\lambda\ge1$ is the paper's standing assumption.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 13, Lemma 4 and Algorithm 1 (proof in Appendix B.2, p. 31)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Lemma 4, p. 13: with `λ`-Lipschitz queries and `δ ∈ (0,1)`, BinSearch (Algorithm 1)
returns within a number of iterations polynomial in `n`, `log λ` and `log (1/δ)` (with a
universal polynomial), and what it returns is a `δ`-ripple division. -/
theorem lemma_4 : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam δ : ℝ), 1 ≤ n → IsInstance f →
    1 ≤ lam → QueriesLipschitz f lam → 0 < δ → δ < 1 →
    ∃ T : ℕ, bsStops f δ T ∧ (∀ k < T, ¬ bsStops f δ k) ∧
      (T : ℝ) ≤ c * ((n : ℝ) + Real.logb 2 lam + Real.logb 2 (1 / δ) + 1) ^ c ∧
      IsRipple f δ (bsOutput f δ T) := by sorry

end MLRPCake.EnvyFree
