-- Prove2me | Theorems.Thm_GuthMaynard_norm_sum_cpow_sub_dual_window_le
-- name    : GuthMaynard.norm_sum_cpow_sub_dual_window_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T02:42:33.377071+00:00
-- url     : https://prove2.me/theorems/86a4e010-4534-4893-86b1-4cb134ad8731
-- title:
--   B-process with endpoint terms — ∑_{a<n≤b} n^{iu} is G times a dual sum, up to endpoint and log errors
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $a, b$ be integers with $1 \le a < b \le 8a$, and let $u \ge 1$ be real. Then there is a complex number $G$ with $|G| \le C\sqrt u$ such that
--   $$\Big|\sum_{a<n\le b} n^{iu} - G\sum_{\lceil u/2\pi b\rceil \le \nu \le \lfloor u/2\pi a\rfloor}\nu^{-1}\nu^{-iu}\Big| \le C\Big(\frac bu + E\Big(\frac{u}{2\pi a}\Big) + E\Big(\frac{u}{2\pi b}\Big) + \log(u+2)\Big).$$
--   Here $E(x) = \dfrac{A}{1 + A\,\|x\|}$, where $A = b/\sqrt u$ and $\|x\| = |x - \mathrm{round}(x)|$ is the distance from $x$ to a nearest integer. Up to a factor $2$, $E(x)$ equals $\min(A, 1/\|x\|)$. The dual sum is empty when $\lfloor u/2\pi a\rfloor < \lceil u/2\pi b\rceil$.
--
--   This is van der Corput's B-process: Kerr's Lemma 26 (B. Kerr, *Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function*, arXiv:1909.12075v1, p. 23), and `GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum`, with one refinement. The error is $N/\sqrt t$ in those versions. Here it is replaced by the two endpoint terms $E$, which are small unless an endpoint $u/(2\pi a)$ or $u/(2\pi b)$ of the dual range lies near an integer.
--
--   **Formalization note.** The endpoint terms are kept so that they can be averaged over $a$ and $b$ (`GuthMaynard.sum_endpoint_term_le`). It is a step of a proof of Jutila's large values estimate (1.2) at $q = 1$ (`GuthMaynard.card_le_of_large_values_jutila_q_one`). The term $b/u$ bounds the zero frequency.
-- source:
--   Kerr, B., Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 23, a refinement of Lemma 26 (the B-process) that keeps the endpoint terms, a step of the proof of Jutila (1.2) at q = 1 (Acta Arith. 32 (1977), p. 56)

import Mathlib

namespace GuthMaynard

theorem norm_sum_cpow_sub_dual_window_le : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ 8 * a →
    ∀ u : ℝ, 1 ≤ u → ∃ G : ℂ, ‖G‖ ≤ C * Real.sqrt u ∧
      ‖(∑ n ∈ Finset.Ioc a b, (n : ℂ) ^ ((u : ℂ) * Complex.I)) -
          G * ∑ ν ∈ Finset.Icc ⌈u / (2 * Real.pi * b)⌉₊ ⌊u / (2 * Real.pi * a)⌋₊,
            (ν : ℂ)⁻¹ * (ν : ℂ) ^ (((-u : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (b / u +
          (b / Real.sqrt u) / (1 + (b / Real.sqrt u) *
            |u / (2 * Real.pi * a) - round (u / (2 * Real.pi * a))|) +
          (b / Real.sqrt u) / (1 + (b / Real.sqrt u) *
            |u / (2 * Real.pi * b) - round (u / (2 * Real.pi * b))|) +
          Real.log (u + 2)) := by
  sorry

end GuthMaynard
