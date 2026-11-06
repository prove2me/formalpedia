-- Prove2me | Theorems.Thm_GuthMaynard_norm_dyadic_sum_cpow_le_dual_sum
-- name    : GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:20:20.220991+00:00
-- url     : https://prove2.me/theorems/244bc196-a0a9-4fee-8dd7-95712b97b84a
-- title:
--   Kerr, Lemma 26 — the B-process bound for ∑_{N≤n≤2N} n^{it} by a dual sum of length ≍ t/N
-- statement:
--   There is an absolute constant $C > 0$ such that for every integer $N \ge 1$ and every real $t \ge 10N$ there are integers $L \ge 1$ and $M$ with $L \ge t/(8\pi N)$ and $M \le t/(\pi N) + 1$ such that
--   $$\Big|\sum_{N \le n \le 2N} n^{it}\Big| \le C\Big(\frac{N}{\sqrt t}\,\Big|\sum_{L \le m \le M} m^{it}\Big| + \frac{N}{\sqrt t} + \log(Nt + 2)\Big).$$
--   (An empty sum, $M < L$, is allowed.)
--
--   This is Lemma 26 of B. Kerr, *Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function*, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 23: “Let $N$ be an integer and $t \ge 1$ a real number. We have $$\Big|\sum_{N\le n\le 2N} n^{it}\Big| \ll \frac{N}{t^{1/2}}\max_{M \le t/N}\Big|\sum_{t/2N \le n \le M} n^{it}\Big| + \frac{N}{t^{1/2}} + \log(Nt).$$” Kerr derives it from van der Corput's B-process (Kerr's Lemma 25, citing Iwaniec–Kowalski, *Analytic Number Theory*, AMS 2004, Theorem 8.16) and partial summation. The phase $f(x) = (t/2\pi)\log x$ has $f'$ ranging over $[t/(4\pi N), t/(2\pi N)]$ on $[N, 2N]$, so the dual sum runs over $t/(4\pi N) \le m \le t/(2\pi N)$, with the weights $|f''(x_m)|^{-1/2} \asymp N t^{-1/2}$ decreasing in $m$.
--
--   **Formalization note.** The printed ranges ($t/2N \le n \le M \le t/N$) omit the factor $2\pi$ of the stationary points $x_m = t/(2\pi m)$. The statement here asserts only that some range inside $[t/(8\pi N), t/(\pi N) + 1]$ works, which contains the dual range $[t/(4\pi N), t/(2\pi N)]$ with room. It asks $t \ge 10N$, the range in which Kerr applies it (Kerr's Lemma 27 assumes $\Delta \gg N$), and has $\log(Nt+2)$ in place of $\log(Nt)$. In this package it is the one analytic input of a reduction of Heath-Brown's large values estimate, Guth–Maynard Theorem 1.6 (`GuthMaynard.heath_brown_large_values`), following Kerr's §§5–6.
-- source:
--   Kerr, B., Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 23, Lemma 26 (van der Corput B-process bound), with explicit ranges, used to reduce Guth–Maynard Theorem 1.6 (Heath-Brown) (arXiv:2405.20552v2, p. 4)

import Mathlib

namespace GuthMaynard

theorem norm_dyadic_sum_cpow_le_dual_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 10 * N ≤ t →
      ∃ L M : ℕ, 1 ≤ L ∧ t / (8 * Real.pi * N) ≤ L ∧ (M : ℝ) ≤ t / (Real.pi * N) + 1 ∧
        ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
          C * (N / Real.sqrt t * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ +
            N / Real.sqrt t + Real.log (N * t + 2)) := by
  sorry

end GuthMaynard
