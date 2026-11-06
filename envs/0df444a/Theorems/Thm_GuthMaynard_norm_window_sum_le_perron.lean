-- Prove2me | Theorems.Thm_GuthMaynard_norm_window_sum_le_perron
-- name    : GuthMaynard.norm_window_sum_le_perron
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T02:42:35.907205+00:00
-- url     : https://prove2.me/theorems/d194b4ce-092b-4c36-b6f8-f8206adebe88
-- title:
--   Discrete Perron formula — a window of a Dirichlet polynomial is bounded by shifts of the full sum
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $A, B, L, M, K$ be natural numbers with $1 \le A$, $B \le 20A$, $A \le L$, $M \le B$ and $K \ge 1$. Let $(c_\nu)$ be complex numbers with $|c_\nu| \le 1$, and let $v$ be real. Then
--   $$\Big|\sum_{L\le\nu\le M}c_\nu\,\nu^{iv}\Big| \le \sum_{\mu=-K}^{K} w_\mu\,\Big|\sum_{A\le\nu\le B}c_\nu\,\nu^{i(v + \pi\mu/2)}\Big| + C\,\frac{B^2}{K},$$
--   with $w_0 = 1$ and $w_\mu = 1/(\pi|\mu|)$ for $\mu \ne 0$.
--
--   The point is that the weights $w_\mu$ and the shifts $\pi\mu/2$ do not depend on $L$ or $M$. A sum over a window $[L, M]$ is therefore controlled by the full sum over $[A, B]$, evaluated at a few shifted points. Moreover $\sum_{|\mu|\le K}w_\mu \ll \log K$.
--
--   **Formalization note.** This is an auxiliary step, not a claim of Jutila's paper. It belongs to a proof of Jutila's large values estimate (1.2) at $q = 1$ (`GuthMaynard.card_le_of_large_values_jutila_q_one`; M. Jutila, *Zero-density estimates for $L$-functions*, Acta Arith. 32 (1977) 55–62, https://doi.org/10.4064/aa-32-1-55-62). There it moves the $u$-dependent dual range of the B-process onto a fixed range.
-- source:
--   Jutila, M., Zero-density estimates for L-functions, Acta Arith. 32 (1977) 55–62, https://doi.org/10.4064/aa-32-1-55-62, p. 56, an auxiliary step (a discrete Perron formula) of a proof of (1.2) at q = 1

import Mathlib

namespace GuthMaynard

theorem norm_window_sum_le_perron : ∃ C : ℝ, 0 < C ∧ ∀ (A B L M K : ℕ) (c : ℕ → ℂ) (v : ℝ),
    1 ≤ A → B ≤ 20 * A → A ≤ L → M ≤ B → 1 ≤ K → (∀ ν, ‖c ν‖ ≤ 1) →
    ‖∑ ν ∈ Finset.Icc L M, c ν * (ν : ℂ) ^ ((v : ℂ) * Complex.I)‖ ≤
      ∑ μ ∈ Finset.Icc (-(K : ℤ)) K,
        (if μ = 0 then 1 else 1 / (Real.pi * |(μ : ℝ)|)) *
          ‖∑ ν ∈ Finset.Icc A B, c ν * (ν : ℂ) ^ (((v + Real.pi * μ / 2 : ℝ) : ℂ) * Complex.I)‖ +
        C * (B : ℝ) ^ 2 / K := by
  sorry

end GuthMaynard
