-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_3_6
-- name    : MDPFinance.OptimalStopping.theorem_10_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:46:47.467822+00:00
-- url     : https://prove2.me/theorems/e36249ba-a05d-4ed0-aa4f-bc3001127b4e
-- title:
--   Theorem 10.3.6 — the Bayesian stopping problem in closed form
-- statement:
--   **Theorem 10.3.6** (p. 326), for the exponential-offer, Inverse-Gamma-prior instance of the
--   Bayesian stopping problem (Example 10.3.5).
--
--   a) The functions $c_{N-k}$ separate in the variables: $c_{N-k}(s,k) = (b+s)\hat c_{N-k}$,
--      $k = 0,\dots,N-1$, and the $\hat c_k$ satisfy the recursion
--      $$ \hat c_1 = \frac{1}{N+a-2}, \qquad
--      \hat c_{N-k+1} = \frac{1}{k+a-2}\Big[(k+a-1)\hat c_{N-k} + \big((1-\hat c_{N-k})^+\big)^{k+a-1}\Big]. $$
--      Moreover the $\hat c_k$ are increasing in $k$, and we define
--      $n^* = n^*(N) := \max\{k \in \{1,\dots,N\} \mid \hat c_{N-k+1} \ge 1\}$ with
--      $\max\emptyset := 0$.
--   b) The $\hat c_k$ are decreasing in the time horizon $N$ and $n^*$ is increasing in $N$.
--   c) The optimal policy $(f_N^*,\dots,f_1^*)$ satisfies $f_{N-k}^* \equiv 0$ for $k = 0,\dots,n^*-1$.
--   d) The maximal expected reward of the Bayesian stopping problem is given by
--      $J_N(0,(0,0)) = b\,\hat c_N$.
--
--   The chapter's most concrete result: an infinite-dimensional Bayesian stopping problem collapses,
--   for this conjugate family, to a one-dimensional recursion.
--
--   **The last term of the recursion is a power, not a quotient.** It is
--   $\big((1-\hat c_{N-k})^+\big)^{k+a-1}$, raised to the exponent $k+a-1$. The text extraction of that
--   line drops the exponent's braces, and the reading of it as a division
--   $(1-\hat c_{N-k})^+/(k+a-1)$ is wrong; the form above is confirmed against a 400 dpi render of the
--   page. The exponent is real, not natural, since $a > 1$ is a real shape parameter.
--
--   **a)'s separation is the whole point** and is what makes the rest computable: $c_{N-k}(s,k)$
--   depends on the accumulated offer total $s$ only through the factor $(b+s)$.
--
--   **b) compares across horizons**, so $\hat c$ is indexed by the horizon $N$ as well as by $k$; a
--   statement about one fixed $N$ could not express it.
--
--   **c) says the first $n^*$ stages never stop.** $f_{N-k}^* \equiv 0$ means "continue in every
--   state"; since the optimal rule stops exactly where $x \ge c_{N-k}((s,k))$, that is the assertion
--   that $x < c_{N-k}((s,k))$ at every **reachable** state of stage $k$. Reachability is carried
--   explicitly as $0 \le x \le s$: $s$ is the accumulated total of the offers seen and $x$ is the
--   current one, so $x \le s$ always, and it is exactly this that $\hat c_{N-k} \ge 1$ turns into
--   $x < (b+s)\hat c_{N-k}$. Dropping it would make c) false, since $x$ would be free to exceed any
--   threshold.
--
--   **Moderation note.** Checked against pp. 326-328; unchanged (the recursion clauses are definitional for `ĉ`, the content is the separation, the monotonicity in `k` and `N`, c) on the reachable states `0 ≤ x ≤ s`, and d)).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 326 (PDF 334), Theorem 10.3.6

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.3.6** (p. 326), Example 10.3.5. a) `c_{N-k}(s,k) = (b+s) ĉ_{N-k}` for
`k = 0,…,N-1`, the `ĉ` satisfy the recursion `ĉ_1 = 1/(N+a-2)`, `ĉ_{N-k+1} = (1/(k+a-2))
[(k+a-1) ĉ_{N-k} + ((1-ĉ_{N-k})^+)^{k+a-1}]`, and are increasing in `k`; `n^*(N) := max{k ∈
{1,…,N} | ĉ_{N-k+1} ≥ 1}`. b) The `ĉ_k` are decreasing in `N` and `n^*` increasing in `N`.
c) `f^*_{N-k} ≡ 0` for `k = 0,…,n^*-1` (on the reachable states `0 ≤ x ≤ s`). d) `J_N(0,(0,0)) =
b ĉ_N`. -/
theorem theorem_10_3_6 (M : BayesStopping) (N : ℕ) (hN : 1 ≤ N) :
    ((∀ (k : ℕ) (s : ℝ), k ≤ N - 1 → 0 ≤ s →
        M.cfun (N - k) s k = (M.b + s) * M.chat N (N - k)) ∧
      (M.chat N 1 = 1 / ((N : ℝ) + M.a - 2)) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ N - 1 →
        M.chat N (N - k + 1)
          = (1 / ((k : ℝ) + M.a - 2)) *
              (((k : ℝ) + M.a - 1) * M.chat N (N - k)
                + Real.rpow (max (1 - M.chat N (N - k)) 0) ((k : ℝ) + M.a - 1))) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ N → M.chat N j ≤ M.chat N k)) ∧
    ((∀ (k N₁ N₂ : ℕ), 1 ≤ k → k ≤ N₁ → N₁ ≤ N₂ → M.chat N₂ k ≤ M.chat N₁ k) ∧
      (∀ N₁ N₂ : ℕ, N₁ ≤ N₂ → M.nStar N₁ ≤ M.nStar N₂)) ∧
    (∀ (k : ℕ) (x s : ℝ), k + 1 ≤ M.nStar N → 0 ≤ x → x ≤ s →
      x < M.cfun (N - k) s k) ∧
    (M.J N 0 0 0 = M.b * M.chat N N) := by sorry

end MDPFinance.OptimalStopping
