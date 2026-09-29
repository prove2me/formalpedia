-- Prove2me | Theorems.Thm_Gilbreath_halved_prime_gap_conditions
-- name    : Gilbreath.halved_prime_gap_conditions
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T00:43:20.622784+00:00
-- url     : https://prove2.me/theorems/0b032e58-5f23-489e-a408-29403158b211
-- title:
--   Cutoff and obstruction conditions for halved prime gaps
-- statement:
--   Let $b : \mathbb{N} \to \mathbb{N}$ satisfy $d^1(n+1) = 2b_n$ for all $n$, where $d^1$ is the prime-gap row of the Gilbreath triangle. Then there is a finite cutoff $N_0$ such that the bottom entry of every $b$-triangle of length at most $N_0$ is $0$ or $1$, and for every larger length $N$ one can choose parameters $N', M, L$ and scales $R$ satisfying the inequalities of the Chase--Hunter--Tao deterministic criterion, under which the initial entries of $b$ are bounded by $2^M$, no row of the $b$-triangle contains $L$ consecutive zeros in range, and the specified right-hand region contains no long block taking only the values $0$ and $d$.
--
--   This is the open combinatorial core of the prime-gap finite-criterion conditions: it is what remains after the (proved) positive normalization of the prime-gap tail supplies the sequence $b$. Together with the proved finite criterion, these conditions imply that every $b$-triangle bottom is $0$ or $1$.
--
--   **Formalization Note** Extracted verbatim from the second half of `Gilbreath.prime_gap_finite_criterion_conditions` for use in a proof-sketch decomposition: it is the conclusion of the parent for an arbitrary sequence satisfying the normalization hypothesis. Like its parent, this is a new conjecture motivated by the paper below, not a claim made there.
-- source:
--   Open core extracted from Gilbreath.prime_gap_finite_criterion_conditions (itself a new conjecture formulated for Prove2Me decomposition by EvanLLL); motivated by Z. Chase, Z. Hunter, T. Tao, Gilbreath's conjecture: a Cramer random model and a deterministic analysis, arXiv:2607.08712v1, pp. 7-8, Theorem 1.6, equations (1.6)-(1.8), https://arxiv.org/pdf/2607.08712v1. The paper calls the obstruction exclusions plausible but does not assert this prime-specific quantified conjecture.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem halved_prime_gap_conditions (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) :
    ∃ N₀ : ℕ,
      (∀ N, 1 ≤ N → N ≤ N₀ →
        iterAbsDiff b (N - 1) 0 = 0 ∨
        iterAbsDiff b (N - 1) 0 = 1) ∧
      (∀ N, N₀ < N →
        ∃ N' M L : ℕ, ∃ R : ℕ → ℕ,
          (1 ≤ N' ∧ N' ≤ N ∧ 1 ≤ M ∧ 1 ≤ L ∧
            1 < R 0 ∧
            (∀ m, m < M → R m < R (m + 1)) ∧
            2 * R M + N' < N ∧
            (∀ m, 1 ≤ m → m ≤ M → 4 * R (m - 1) ≤ R m) ∧
            100 * L * 8 ^ M ≤ R 0) ∧
          (∀ j < N, b j ≤ 2 ^ M) ∧
          (¬ ∃ i j : ℕ,
            i + L ≤ N ∧ j + i + L ≤ N ∧
            ∀ t < L, iterAbsDiff b i (j + t) = 0) ∧
          (¬ ∃ m d' i k j : ℕ,
            1 ≤ m ∧ m ≤ M ∧
            2 ^ (M - m) < d' ∧ d' ≤ 2 ^ (M - m + 1) ∧
            i ≤ 2 * R (m - 1) ∧
            R m ≤ k + 3 * R (m - 1) ∧
            N' ≤ j + 1 ∧ j + i + k + 1 ≤ N ∧
            ∀ t < k, iterAbsDiff b i (j + t) = 0 ∨
              iterAbsDiff b i (j + t) = d')) := by sorry
end Gilbreath
