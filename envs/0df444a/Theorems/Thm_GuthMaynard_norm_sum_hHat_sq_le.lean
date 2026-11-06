-- Prove2me | Theorems.Thm_GuthMaynard_norm_sum_hHat_sq_le
-- name    : GuthMaynard.norm_sum_hHat_sq_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:22:18.088142+00:00
-- url     : https://prove2.me/theorems/18635299-7cbd-42b3-8865-564364d0e3b0
-- title:
--   Approximate functional equation for ∑ ĥ_t(mN), squared (Guth–Maynard Lemma 6.2 form)
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. Write $G(x) = e^x w(e^x)^2$ and $\widehat G$ for its Fourier transform. Then there are $C$ and $T_0$ such that for all $T \ge T_0$, all integers $N \ge 1$ and $1 \le M \le T^2$, and every real $t$ with $|t| \ge T^{\varepsilon}$,
--   $$\Big|\sum_{1\le m\le M}\widehat h_t(mN)\Big|^2 \le \frac{C}{|t|}\int_{\mathbb R}|\widehat G(\rho)|\,\Big|\sum_{1\le m\le M} m^{-i(t+2\pi\rho)}\Big|^2 d\rho + T^{-100},$$
--   where $\widehat h_t(\xi) = \int e(-\xi u)\,w(u)^2u^{it}\,du$ (`hHat w t ξ`).
--
--   This is a squared form of Guth–Maynard's Lemma 6.2, the approximate functional equation (p. 17, proved on pp. 19–20, arXiv:2405.20552v2). It uses Fourier inversion of $G$ in the variable $x = \log u$, which is Mellin inversion of $w^2$ on the line $\operatorname{Re} s = 1$ ($s = 1 - 2\pi i\rho$). It also uses the bound $\big|\int_a^b v^{-1+i\tau}e(-v)\,dv\big| \ll |\tau|^{-1/2}$. Here, unlike the lemma as printed, $M$ is a free parameter and the $\rho$-integral is not truncated. It is published separately so that the proof of Proposition 6.1 (`GuthMaynard.norm_S_two_le`) fits the verifier's time limit.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 17–20, Lemma 6.2 (approximate functional equation), squared form used in the proof of Proposition 6.1

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem norm_sum_hHat_sq_le (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N M : ℕ, 1 ≤ N → 1 ≤ M → (M : ℝ) ≤ T ^ 2 →
      ∀ t : ℝ, T ^ ε ≤ |t| →
        ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
          C / |t| * (∫ ρ : ℝ,
            ‖FourierTransform.fourier (fun x : ℝ => ((Real.exp x * w (Real.exp x) ^ 2 : ℝ) : ℂ)) ρ‖ *
              ‖∑ m ∈ Finset.Icc 1 M,
                (m : ℂ) ^ (((-(t + 2 * Real.pi * ρ) : ℝ) : ℂ) * Complex.I)‖ ^ 2) +
            T ^ (-100 : ℝ) := by
  sorry

end GuthMaynard
