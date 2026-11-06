-- Prove2me | Theorems.Thm_GuthMaynard_maynard_pratt_typeI_or_typeII
-- name    : GuthMaynard.maynard_pratt_typeI_or_typeII
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:03:59.911909+00:00
-- url     : https://prove2.me/theorems/c44b67a1-372b-408c-8286-df78d98abba2
-- title:
--   Maynard–Pratt, Lemma 23 — every zero with γ ∈ [T, 2T] is of Type I or of Type II
-- statement:
--   There is $T_0$ such that for all $T \ge T_0$ the following holds. Let
--   $$D_N(s) = \sum_{N<n\le 2N} a(n)\exp\Big(-\frac{n}{T^{1/2}}\Big)n^{-s}, \qquad a(n) = \sum_{d\mid n,\ d\le 2T^{1/100}}\mu(d), \qquad M(s) = \sum_{1\le m\le 2T^{1/100}}\mu(m)m^{-s}.$$
--   Then every zero $\rho = \beta + i\gamma$ of $\zeta$ with $\gamma \in [T, 2T]$ satisfies at least one of:
--   - (Type I) $|D_N(\rho)| \ge 1/(3\log T)$ for some $N = 2^j$ with $T^{1/100} \le N \le T^{1/2}(\log T)^2$;
--   - (Type II) $\Big|\frac{1}{2\pi}\int_{-\infty}^{\infty}T^{s/2}\,\Gamma(s)\,M(\rho+s)\,\zeta(\rho+s)\,du\Big| \ge \frac13$, where $s = \tfrac12 - \beta + iu$.
--
--   This is Lemma 23 of J. Maynard and K. Pratt, *Half-isolated zeros and zero-density estimates*, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, pp. 14–16, whose page numbers are used): “**Lemma 23.** Let $T$ be sufficently large. Then every non-trivial zero $\rho = \beta + i\gamma$ with $\gamma \in [T, 2T]$ is either a Type I zero or a Type II zero (or both).” Their Definition 22 (pp. 15–16) defines a Type I zero by “$|D_N(\rho)| \ge \frac{1}{3\log T}$ (18) for some $N = 2^j \in [T^{1/100}, T^{1/2}(\log T)^2]$”, with $D_N$ as in their (15)–(16), and a Type II zero by “$\Big|\frac{1}{2\pi i}\int_{(-\beta+1/2)}T^{s/2}\Gamma(s)M(\rho+s)\zeta(\rho+s)\,ds\Big| \ge \frac13$ (19)”. Their notation (p. 6) is “$n \sim N$ for the condition $N < n \le 2N$”. Guth–Maynard (arXiv:2405.20552v2, p. 48) use this lemma together with Lemma 24, `GuthMaynard.maynard_pratt_card_typeII_zeros_le`, as the milestone `GuthMaynard.card_not_typeI_zeros_le`.
--
--   **Formalization note.**
--   - The line integral $\frac{1}{2\pi i}\int_{(c)}f(s)\,ds$ is written as $\frac{1}{2\pi}\int_{\mathbb R}f(c + iu)\,du$ with $c = \tfrac12 - \beta$.
--   - The zeros of $\zeta$ with $\gamma \in [T, 2T]$ and $T \ge 1$ are exactly the non-trivial zeros with that ordinate, so "non-trivial" is not stated separately.
--   - The proof in Appendix C (p. 36) assumes $\beta \ge \frac12 + \frac{1}{\log T}$. The lemma as printed has no such hypothesis, and it is stated here as printed.
-- source:
--   Maynard, J. and Pratt, K., Half-isolated zeros and zero-density estimates, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, whose page numbers are used), pp. 14–16, Lemma 23 (with Definitions 17 and 22), used in Guth–Maynard (arXiv:2405.20552v2), p. 48

import Mathlib

namespace GuthMaynard

theorem maynard_pratt_typeI_or_typeII :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let D : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Ioc N (2 * N),
        ((∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ)) * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) *
          (n : ℂ) ^ (-s)
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ∈ Set.Icc T (2 * T) →
        (∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
            1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖) ∨
        1 / 3 ≤ ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          let s : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I
          (T : ℂ) ^ (s / 2) * Complex.Gamma s * M (ρ + s) * riemannZeta (ρ + s)‖ := by
  sorry

end GuthMaynard
