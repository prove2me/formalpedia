-- Prove2me | Theorems.Thm_GuthMaynard_integral_norm_riemannZeta_half_pow_four_le
-- name    : GuthMaynard.integral_norm_riemannZeta_half_pow_four_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T21:56:45.398196+00:00
-- url     : https://prove2.me/theorems/1a5bb977-d3ca-476d-bbe9-292e4064bc1d
-- title:
--   Fourth moment of ζ on the critical line — ∫₀ᵀ |ζ(1/2+it)|⁴ dt ≪ T (1 + log T)⁹
-- statement:
--   There is a constant $C \ge 0$ such that for all $T \ge 2$,
--   $$\int_0^T\big|\zeta(\tfrac12+it)\big|^4\,dt \le C\,T\,(1+\log T)^9.$$
--
--   This is a weak form of Ingham's fourth-moment asymptotic $\int_0^T|\zeta(\frac12+it)|^4\,dt \sim \frac{1}{2\pi^2}T\log^4T$ (published as `LindelofHypothesis.fourth_moment_asymptotic`). It is not a claim of M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933.
--
--   On p. 169 that paper counts its class (ii) zeros with a discrete fourth moment: “by a lemma of Montgomery [6, 7] when $t_1, \dots, t_R$ satisfy (2.4) then $\sum_1^R|\zeta(\frac12+it_r)|^4 \ll Tl^5$” (6.2). A proof of (1.9) for $3/4 \le \alpha \le 9/11$, `GuthMaynard.huxley_density_estimate_of_le_nine_elevenths`, counts those zeros with this continuous bound instead. The power $9$ of the logarithm is enough there, because the class (ii) count is then $\ll T^{3(1-\alpha)/(3\alpha-1)}(\log T)^{10}$, against the $(\log T)^{44}$ of (1.9).
--
--   **Formalization note.** The integral is Mathlib's interval integral over $[0, T]$. The integrand is continuous, so this is the Lebesgue integral.
-- source:
--   Huxley, M. N., On the difference between consecutive primes, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, p. 169, a fourth-moment bound for zeta on the critical line, used in place of Montgomery's (6.2), an auxiliary step of a proof of (1.9) for 3/4 ≤ α ≤ 9/11

import Mathlib

namespace GuthMaynard

theorem integral_norm_riemannZeta_half_pow_four_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 ≤
        C * T * (1 + Real.log T) ^ 9 := by
  sorry

end GuthMaynard
