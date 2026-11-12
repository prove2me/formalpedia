-- Prove2me | Theorems.Thm_GuthMaynard_maynard_pratt_twisted_fourth_moment
-- name    : GuthMaynard.maynard_pratt_twisted_fourth_moment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T19:23:26.162861+00:00
-- url     : https://prove2.me/theorems/3217d567-0c2b-4d87-b742-a4a8a92e3f44
-- title:
--   Maynard–Pratt, Appendix C — twisted fourth moment ∫_{T/2}^{3T} |M ζ(1/2+it)|^4 dt ≪ T (log T)^{O(1)}
-- statement:
--   There are constants $A$, $C$ and $T_0$ such that for all $T \ge T_0$,
--   $$\int_{T/2}^{3T}\big|M(\tfrac12+it)\,\zeta(\tfrac12+it)\big|^4\,dt \le C\,T\,(\log T)^A, \qquad M(s) = \sum_{1\le m\le 2T^{1/100}}\mu(m)m^{-s}.$$
--
--   This is the bound used in the proof of Lemma 24 of J. Maynard and K. Pratt, *Half-isolated zeros and zero-density estimates*, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, p. 38, whose page numbers are used): “By bounds for the twisted fourth moment of the zeta function (see [13, Theorem 1.1], [2, Theorem 1.2], or [9, Proposition 5.1]) we have $\int_{T/2}^{3T}\big|M\big(\frac12+it\big)\zeta\big(\frac12+it\big)\big|^4dt \ll T(\log T)^{O(1)}$”. The mollifier is their $M(s) := \sum_{m\le 2T^{1/100}}\frac{\mu(m)}{m^s}$ of (19), p. 16. Their references are [13] C. P. Hughes and M. P. Young, *The twisted fourth moment of the Riemann zeta function*, J. Reine Angew. Math. 641 (2010), https://doi.org/10.1515/crelle.2010.034; [2] S. Bettin, H. M. Bui, X. Li and M. Radziwiłł, *A quadratic divisor problem and moments of the Riemann zeta-function*, J. Eur. Math. Soc. 22 (2020) 3953–3980, https://doi.org/10.4171/jems/999; [9] W. Heap, M. Radziwiłł and K. Soundararajan, *Sharp upper bounds for fractional moments of the Riemann zeta function*, Q. J. Math. 70 (2019) 1387–1396, https://doi.org/10.1093/qmathj/haz027. Lemma 24, `GuthMaynard.maynard_pratt_card_typeII_zeros_le`, is reduced to this statement.
--
--   **Formalization note.**
--   - "$T$ large" is the threshold $T_0$, and the exponent $O(1)$ is one constant $A$.
--   - The integral is Mathlib's interval integral; the integrand is continuous, so it is the Lebesgue integral over $[T/2, 3T]$.
-- source:
--   Maynard, J. and Pratt, K., Half-isolated zeros and zero-density estimates, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, whose page numbers are used), p. 38, the twisted fourth moment bound in the proof of Lemma 24 (Appendix C), cited there from Hughes–Young, Thm 1.1; Bettin–Bui–Li–Radziwiłł, Thm 1.2; Heap–Radziwiłł–Soundararajan, Prop. 5.1

import Mathlib

namespace GuthMaynard

theorem maynard_pratt_twisted_fourth_moment :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∫ t in T / 2..3 * T,
          ‖M (1 / 2 + (t : ℂ) * Complex.I) * riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 ≤
        C * T * Real.log T ^ A := by
  sorry

end GuthMaynard
