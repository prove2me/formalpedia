-- Prove2me | Theorems.Thm_GuthMaynard_twisted_fourth_moment_dyadic_gaussian
-- name    : GuthMaynard.twisted_fourth_moment_dyadic_gaussian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:20:46.618816+00:00
-- url     : https://prove2.me/theorems/6a1aa5d0-e56c-4780-9fb3-0b320676deff
-- title:
--   Twisted fourth moment of a smooth dyadic block of zeta's Dirichlet series, in a Gaussian window
-- statement:
--   There is a function $V : \mathbb{R} \to [0, 1]$, vanishing outside $(\tfrac12, 2)$, with
--   $$\sum_{j=0}^{J} V(x/2^j) = 1 \qquad (1 \le x \le 2^J)$$
--   for every natural number $J$, and there are real constants $C$, $A_0$, $T_0$, with the following property. Let $T \ge T_0$ and put $\Delta = T/\log T$. Let $j \ge 0$ be an integer with $2^j \le 4\sqrt T$, and let $t_0$, $u$ be real with $T/2 \le t_0 \le 4T$ and $|u| \le 2T^{3/4}$. Then
--   $$\int_{-\infty}^{\infty} e^{-((t - t_0)/\Delta)^2}\,\Big|\sum_{\nu \le 2^{j+1}} V(\nu/2^j)\,\nu^{-1/2 + i(u - t)}\Big|^4\,\big|M(\tfrac12 + it)\big|^4\,dt \le C\,\Delta\,(\log T)^{A_0}, \qquad M(s) = \sum_{1 \le m \le 2T^{1/100}}\mu(m)m^{-s}.$$
--
--   So the fourth moment of a smooth dyadic piece of $\sum_\nu \nu^{-1/2 - it}$, twisted by the fourth power of a mollifier of length $2T^{1/100}$, is of the expected size in a window of width $T/\log T$ around any $t_0$ of size $T$, uniformly in a shift $u$.
--
--   **Formalization note.**
--   - This is an auxiliary step, not a claim of any cited paper. The twisted fourth moment bound `GuthMaynard.maynard_pratt_twisted_fourth_moment` is reduced to it. That bound is applied by Maynard and Pratt in the proof of their Lemma 24 (J. Maynard and K. Pratt, *Half-isolated zeros and zero-density estimates*, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191).
--   - The function $V$ is asserted to exist and is not specified. Only the listed properties are stated: values in $[0, 1]$, $V(x) = 0$ for $x \le \tfrac12$ and for $x \ge 2$, and the partition identity.
--   - The constants $C$, $A_0$, $T_0$ are real numbers with no sign condition, and $(\log T)^{A_0}$ is a real power.
--   - The sum over $\nu$ runs over $1 \le \nu \le 2 \cdot 2^j$.
-- source:
--   Maynard, J. and Pratt, K., Half-isolated zeros and zero-density estimates, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, whose page numbers are used), p. 38, an auxiliary step (one smooth dyadic block in a Gaussian window) of a proof of the twisted fourth moment bound in the proof of Lemma 24

import Mathlib

namespace GuthMaynard

theorem twisted_fourth_moment_dyadic_gaussian :
    ∃ V : ℝ → ℝ, (∀ x : ℝ, 0 ≤ V x ∧ V x ≤ 1) ∧ (∀ x : ℝ, x ≤ 1 / 2 → V x = 0) ∧
      (∀ x : ℝ, 2 ≤ x → V x = 0) ∧
      (∀ (J : ℕ) (x : ℝ), 1 ≤ x → x ≤ 2 ^ J → ∑ j ∈ Finset.range (J + 1), V (x / 2 ^ j) = 1) ∧
      ∃ C A₀ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (j : ℕ) (t₀ u : ℝ), (2 : ℝ) ^ j ≤ 4 * Real.sqrt T →
        T / 2 ≤ t₀ → t₀ ≤ 4 * T → |u| ≤ 2 * T ^ (3 / 4 : ℝ) →
        ∫ t : ℝ, Real.exp (-((t - t₀) / (T / Real.log T)) ^ 2) *
            ‖∑ ν ∈ Finset.Icc (1 : ℕ) (2 * 2 ^ j), ((V ((ν : ℝ) / 2 ^ j) : ℝ) : ℂ) *
              (ν : ℂ) ^ (-(1 / 2 : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I)‖ ^ 4 *
            ‖∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊, (ArithmeticFunction.moebius m : ℂ) *
              (m : ℂ) ^ (-(1 / 2 + (t : ℂ) * Complex.I))‖ ^ 4 ≤
          C * (T / Real.log T) * Real.log T ^ A₀ := by
  sorry

end GuthMaynard
