-- Prove2me | Theorems.Thm_GuthMaynard_card_not_typeI_zeros_le
-- name    : GuthMaynard.card_not_typeI_zeros_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T19:16:20.00589+00:00
-- url     : https://prove2.me/theorems/0c579576-da51-4323-b26b-a9cfd5f119f9
-- title:
--   Zero detection — the zeros that are not Type I (Maynard–Pratt, Lemmas 23–24)
-- statement:
--   There are constants $A$, $C$ and $T_0$ such that for all $T \ge T_0$ and every real $\sigma$ the following holds. Let
--   $$D_N(s) = \sum_{N<n\le 2N} b_nn^{-s}, \qquad b_n = \Big(\sum_{d\mid n,\ d\le 2T^{1/100}}\mu(d)\Big)\exp\Big(-\frac{n}{T^{1/2}}\Big).$$
--   Call a zero $\rho$ of $\zeta$ *Type I* if $|D_N(\rho)| \ge 1/(3\log T)$ for some $N = 2^j \in [T^{1/100}, T^{1/2}(\log T)^2]$. Then the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $\operatorname{Im}\rho \in [T, 2T]$ that are not Type I, counted with multiplicity, is at most $C\,T^{2-2\sigma}(\log T)^A$.
--
--   **Formalization note.** This is the combination the paper uses: Maynard–Pratt's Lemma 23 (every such zero is Type I or Type II) and Lemma 24 (the Type II zeros number $\ll T^{2(1-\sigma)}(\log T)^{O(1)}$). The statement is for every real $\sigma$. Lemma 23's proof assumes $\operatorname{Re}\rho \ge 1/2 + 1/\log T$. Zeros with imaginary part in $[T, 2T]$ are non-trivial. They are counted with multiplicity.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 48, zero detection, cited in the proof of Theorem 1.2, which cites Maynard, J. and Pratt, K., Half-isolated zeros and zero-density estimates, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, Lemmas 23 and 24 (arXiv:2206.11729v2), https://doi.org/10.1093/imrn/rnae191

import Mathlib

open scoped ENNReal

namespace GuthMaynard

theorem card_not_typeI_zeros_le :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      let D : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Ioc N (2 * N),
        ((∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ)) * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) *
          (n : ℂ) ^ (-s)
      (((∑' ρ : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧
          ¬ ∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
            1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖}, analyticOrderAt riemannZeta (ρ : ℂ)) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (2 - 2 * σ) * Real.log T ^ A) := by
  sorry

end GuthMaynard
