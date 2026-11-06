-- Prove2me | Theorems.Thm_GuthMaynard_maynard_pratt_card_typeII_zeros_le
-- name    : GuthMaynard.maynard_pratt_card_typeII_zeros_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T21:04:03.029176+00:00
-- url     : https://prove2.me/theorems/d125fb26-e15c-4fe9-b889-fbba09540545
-- title:
--   Maynard–Pratt, Lemma 24 — R_II(σ, T) ≪ T^{2(1−σ)} (log T)^{O(1)}
-- statement:
--   There are constants $A$, $C$ and $T_0$ such that for all $T \ge T_0$ and every real $\sigma$, the number of zeros $\rho = \beta + i\gamma$ of $\zeta$ with $\beta \ge \sigma$, $\gamma \in [T, 2T]$ and
--   $$\Big|\frac{1}{2\pi}\int_{-\infty}^{\infty}T^{s/2}\,\Gamma(s)\,M(\rho+s)\,\zeta(\rho+s)\,du\Big| \ge \frac13, \qquad s = \tfrac12 - \beta + iu,\quad M(s) = \sum_{1\le m\le 2T^{1/100}}\mu(m)m^{-s},$$
--   counted with multiplicity, is at most $C\,T^{2-2\sigma}(\log T)^A$.
--
--   This is Lemma 24 of J. Maynard and K. Pratt, *Half-isolated zeros and zero-density estimates*, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, p. 16, whose page numbers are used): “**Lemma 24.** We have $R_{II}(\sigma, T) \ll T^{2(1-\sigma)}(\log T)^{O(1)}$.” Here, on the same page, “$R_{II}(\sigma, T)$ denote[s] the number of Type II zeros with $\beta \ge \sigma$ and $\gamma \in [T, 2T]$”. A Type II zero is defined by their (19) (p. 16): “$\Big|\frac{1}{2\pi i}\int_{(-\beta+1/2)}T^{s/2}\Gamma(s)M(\rho+s)\zeta(\rho+s)\,ds\Big| \ge \frac13$”. The proof (Appendix C, pp. 37–38) uses a twisted fourth moment of $\zeta$ on the critical line. Guth–Maynard (arXiv:2405.20552v2, p. 48) cite it as “[MP, Lemma 24]”. Together with Lemma 23, `GuthMaynard.maynard_pratt_typeI_or_typeII`, it gives the milestone `GuthMaynard.card_not_typeI_zeros_le`.
--
--   **Formalization note.**
--   - The line integral is written as $\frac{1}{2\pi}\int_{\mathbb R}f(\tfrac12 - \beta + iu)\,du$.
--   - The count is with multiplicity. Maynard–Pratt do not specify the convention, and their proof's bound by the number of well-spaced points times $(\log T)^4$ covers either.
--   - "$T$ large" is the threshold $T_0$, and the exponent $O(1)$ is one constant $A$.
-- source:
--   Maynard, J. and Pratt, K., Half-isolated zeros and zero-density estimates, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, whose page numbers are used), p. 16, Lemma 24 (with Definition 22), cited in Guth–Maynard (arXiv:2405.20552v2), p. 48

import Mathlib

open scoped ENNReal

namespace GuthMaynard

theorem maynard_pratt_card_typeII_zeros_le :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      (((∑' ρ : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧
          1 / 3 ≤ ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
            let s : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I
            (T : ℂ) ^ (s / 2) * Complex.Gamma s * M (ρ + s) * riemannZeta (ρ + s)‖},
          analyticOrderAt riemannZeta (ρ : ℂ)) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (2 - 2 * σ) * Real.log T ^ A) := by
  sorry

end GuthMaynard
