-- Prove2me | Theorems.Thm_Gilbreath_prime_gap_finite_criterion_conditions
-- name    : Gilbreath.prime_gap_finite_criterion_conditions
-- status  : Open
-- author  : @EvanLLL
-- created : 2026-09-24T23:04:52.21787+00:00
-- url     : https://prove2.me/theorems/db2844c6-0ded-449a-beac-64711a15ca85
-- title:
--   Prime-gap obstruction conditions for the finite Gilbreath criterion
-- statement:
--   Proposed new sufficient-condition conjecture for the actual primes, motivated by Chase–Hunter–Tao's deterministic criterion; the authors do not claim this assertion. Let b be the halved prime-gap tail, so d¹(n+1)=2b(n). There should be a finite cutoff N₀ such that the bottom of every triangle of length at most N₀ is 0 or 1, and for each larger length N one can choose the parameters of Theorem 1.6 so that b has bounded initial entries, no block of L zeros anywhere, and no forbidden long shallow {0,d}-valued block in the specified right-hand region. Together with Theorem 1.6 this would imply the platform's zero-two-blocks theorem.
-- source:
--   New conjectural specialization formulated for this Prove2Me decomposition, motivated by Z. Chase, Z. Hunter, T. Tao, Gilbreath's conjecture: a Cramér random model and a deterministic analysis, arXiv:2607.08712v1, pp. 7–8, Theorem 1.6, equations (1.6)–(1.8), and the discussion immediately following it, https://arxiv.org/pdf/2607.08712v1. The paper calls the obstruction exclusions plausible but does not assert this prime-specific quantified conjecture.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath

-- New open conjecture motivated by the application of Chase--Hunter--Tao,
-- arXiv:2607.08712v1, Theorem 1.6 and the discussion on p. 8.
-- It is not a claim proved or explicitly conjectured in that paper.
theorem prime_gap_finite_criterion_conditions :
    ∃ b : ℕ → ℕ,
      (∀ n, d 1 (n + 1) = 2 * b n) ∧
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
