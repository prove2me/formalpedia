-- Prove2me | Theorems.Thm_GuthMaynard_norm_sum_vonMangoldt_sub_explicit_formula_le
-- name    : GuthMaynard.norm_sum_vonMangoldt_sub_explicit_formula_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:16:37.780572+00:00
-- url     : https://prove2.me/theorems/fd1c2ed1-def1-42be-af86-dbfe57ca7096
-- title:
--   The truncated explicit formula for short intervals (p. 50)
-- statement:
--   There is an absolute constant $C$ such that for all real $x$, $T$, $y$ with $2 \le T \le x$ and $0 \le y \le x$,
--   $$\Big|\sum_{x \le n \le x+y}\Lambda(n) - y + \sum_{|\rho| \le T}\frac{(x+y)^\rho - x^\rho}{\rho}\Big| \le C\,\frac{x(\log x)^3}{T},$$
--   where $\rho$ runs over the zeros of $\zeta$ with $0 < \operatorname{Re}\rho < 1$ and $|\rho| \le T$, counted with multiplicity, and $\Lambda$ is the von Mangoldt function.
--
--   **Formalization note.** The paper states the formula "for any choice of $2 \le T \le x$" with $y$ from the corollaries. Here $0 \le y \le x$ is assumed; the corollaries use $y \le x^{0.99}$. The sum over $\rho$ is over non-trivial zeros, each counted with its multiplicity, and the integers $n$ range over $[x, x+y]$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 50, the truncated explicit formula, in the proof of Corollaries 1.3 and 1.4, which cites Davenport, H., Multiplicative number theory, third edition, Graduate Texts in Mathematics 74, Springer (2000), Chapter 17, https://doi.org/10.1007/978-1-4757-5927-3

import Mathlib

namespace GuthMaynard

theorem norm_sum_vonMangoldt_sub_explicit_formula_le :
    ∃ C : ℝ, ∀ x T y : ℝ, 2 ≤ T → T ≤ x → 0 ≤ y → y ≤ x →
      ‖(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y +
        ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ≤
        C * x * Real.log x ^ 3 / T := by
  sorry

end GuthMaynard
