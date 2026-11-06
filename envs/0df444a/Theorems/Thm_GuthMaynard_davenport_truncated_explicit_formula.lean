-- Prove2me | Theorems.Thm_GuthMaynard_davenport_truncated_explicit_formula
-- name    : GuthMaynard.davenport_truncated_explicit_formula
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T20:21:58.838094+00:00
-- url     : https://prove2.me/theorems/f087183c-55f6-4452-bdfb-39d3a06edd5c
-- title:
--   Davenport, Ch. 17 (9)–(10) — the truncated explicit formula for ψ₀(x)
-- statement:
--   There is an absolute constant $C$ such that for all real $x \ge 2$ and $T \ge 2$,
--   $$\Big|\psi_0(x) - x + \sum_{|\gamma| < T}\frac{x^\rho}{\rho} + \log 2\pi + \tfrac12\log(1 - x^{-2})\Big| \le C\Big(\frac{x\log^2(xT)}{T} + (\log x)\min\Big(1, \frac{x}{T\langle x\rangle}\Big)\Big).$$
--   Here $\psi_0(x) = \sum_{n \le x}\Lambda(n) - \tfrac12\Lambda(x)$ when $x$ is an integer and $\sum_{n\le x}\Lambda(n)$ otherwise; $\rho = \beta + i\gamma$ runs over the zeros of $\zeta$ with $0 < \beta < 1$ and $|\gamma| < T$, each counted with its multiplicity; and $\langle x\rangle$ is the infimum of $|x - n|$ over the prime powers $n \ne x$.
--
--   This is (9)–(10) of H. Davenport, *Multiplicative Number Theory*, Graduate Texts in Mathematics 74, Springer, Chapter 17, p. 113 (a book, cited without a DOI: Guth–Maynard cite the 3rd edition of 2000, and the copy consulted does not show its edition, so page numbers may differ slightly): “(9) $\psi_0(x) = x - \sum_{|\gamma|<T}\frac{x^\rho}{\rho} - \frac{\zeta'(0)}{\zeta(0)} - \frac12\log(1 - x^{-2}) + R(x, T)$, where (10) $|R(x,T)| \ll \frac{x\log^2(xT)}{T} + (\log x)\min\Big(1, \frac{x}{T\langle x\rangle}\Big)$.” On p. 108: “$\zeta'(0)/\zeta(0)$ is $\log 2\pi$”, and “we shall suppose that $x \ge 2$”. On p. 112: “It is convenient to write $\langle x\rangle$ for the distance from $x$ to the nearest prime power, other than $x$ itself in case $x$ is a prime power.” On p. 114 the restriction on $T$ used in the proof is removed. Guth–Maynard (arXiv:2405.20552v2, p. 50) apply the formula through its consequence for $\sum_{x \le n \le x+y}\Lambda(n)$, the milestone `GuthMaynard.norm_sum_vonMangoldt_sub_explicit_formula_le`.
--
--   **Formalization note.** Davenport takes $T$ large; here $T \ge 2$, which only changes the constant. The zeros are those of $\zeta$ in the open strip $0 < \operatorname{Re} s < 1$, with multiplicity the order of vanishing.
-- source:
--   Davenport, H., Multiplicative Number Theory, Graduate Texts in Mathematics 74, Springer (3rd ed. 2000, the edition Guth–Maynard cite), p. 113, Chapter 17, (9)–(10), the truncated explicit formula, applied in Guth–Maynard (arXiv:2405.20552v2), p. 50

import Mathlib

namespace GuthMaynard

theorem davenport_truncated_explicit_formula :
    ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
      ‖(((Chebyshev.psi x -
            (if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0) - x : ℝ)) : ℂ) +
          (∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
            (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) +
          ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ≤
        C * (x * Real.log (x * T) ^ 2 / T +
          Real.log x * min 1 (x / (T * sInf {d : ℝ | ∃ n : ℕ, IsPrimePow n ∧ (n : ℝ) ≠ x ∧
            d = |x - n|}))) := by
  sorry

end GuthMaynard
