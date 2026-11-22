-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_logDeriv_bound_in_zero_free_region
-- name    : MasulloGRH.heckeLFunction_logDeriv_bound_in_zero_free_region
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T18:04:42.200464+00:00
-- url     : https://prove2.me/theorems/b0595c1b-d3fe-4ff8-9080-64b6ab613616
-- title:
--   Proposition B.6.1.1 and Theorem B.6.1.3 — $L_f'(s,\chi)/L_f(s,\chi)\ll\log^2|t|$ in a zero-free region reaching every height
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character, and let $L_f(s,\chi)$ be the finite Hecke $L$-function, continued meromorphically to $\mathbb C$. For $c>0$ let $\mathcal R_c$ be the region of the points $s=\sigma+it$ with
--
--   $$\sigma\ge 1-\frac{c}{\log(|t|+3)} .$$
--
--   1. If $\chi$ is not trivial on $C_F^1$, there are $c>0$ and $C$ such that $L_f(s,\chi)$ is analytic and non-zero at every $s\in\mathcal R_c$, and
--   $$\left|\frac{L_f'(s,\chi)}{L_f(s,\chi)}\right|\le C\,\log^2(|t|+3)\qquad(s\in\mathcal R_c).$$
--
--   2. If $\chi=|\cdot|_F^{-it_0}$ for a real number $t_0$, so that $L_f(s,\chi)=\zeta_F(s-it_0)$, there are $c>0$ and $C$ such that $L_f(s,\chi)$ is analytic and non-zero at every $s\in\mathcal R_c$ other than $1+it_0$, and
--   $$\left|\frac{L_f'(s,\chi)}{L_f(s,\chi)}+\frac{1}{s-(1+it_0)}\right|\le C\,\log^2(|t|+3)\qquad(s\in\mathcal R_c,\ s\ne 1+it_0).$$
--
--   This is the form in which the classical zero-free region and the bound for the logarithmic derivative enter the contour integrals of §B.7: a region of de la Vallée Poussin shape reaching down to every height, in which $L_f'/L_f$, after removal of its polar part at the pole of $L_f$, grows at most like $\log^2|t|$.
--
--   **Formalization Note** The statement combines Proposition B.6.1.1 (zero-free region), Theorem B.6.1.3 (the bound for $L_f'/L_f$ at large ordinates), and Proposition 3.2.1.3 (2)–(3) ($L_f(s,\chi)$ has no pole near $\operatorname{Re}(s)\ge1$ except the simple pole at $1+it_0$ in the second case), together with a bound on the compact part of the region at bounded height, as they are used at the beginning of the proof of Theorem B.7.1.2. The constants $c$ and $C$ may depend on $\chi$. $L_f(s,\chi)$ is `heckeLFunction χ`, the continuation in normal form; the region includes all $s$ with large real part.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.6.1, Proposition B.6.1.1 and Theorem B.6.1.3, as used in the proof of Theorem B.7.1.2, p. 647; §3.2.1, Proposition 3.2.1.3 (2)–(3), p. 123

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_logDeriv_bound_in_zero_free_region
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → ∃ c C : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re →
        AnalyticAt ℂ (heckeLFunction χ) s ∧ heckeLFunction χ s ≠ 0 ∧
        ‖deriv (heckeLFunction χ) s / heckeLFunction χ s‖ ≤ C * Real.log (|s.im| + 3) ^ 2) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ → ∃ c C : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
        AnalyticAt ℂ (heckeLFunction χ) s ∧ heckeLFunction χ s ≠ 0 ∧
        ‖deriv (heckeLFunction χ) s / heckeLFunction χ s + 1 / (s - (1 + t₀ * Complex.I))‖ ≤
          C * Real.log (|s.im| + 3) ^ 2) := by sorry

end MasulloGRH
