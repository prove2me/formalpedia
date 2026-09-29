-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two
-- name    : LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/253cf33c-2e4a-5c61-9838-bcfb6bf55027
-- title:
--   Planar Hecke–Bochner identity for (u₀+ε i u₁)^m
-- statement:
--   Let $m$ be a natural number, let $\varepsilon$ be a real number with $\varepsilon = 1$ or $\varepsilon = -1$, and let $\xi \colon \mathrm{Fin}\,2 \to \mathbb{R}$, i.e. a point $(\xi_0,\xi_1)$ of the plane. Consider the complex-valued function on $\mathrm{Fin}\,2 \to \mathbb{R}$, equipped with its Lebesgue (volume) measure, given by $$u \mapsto (u_0 + \varepsilon i\,u_1)^m \, e^{-\pi(u_0^2+u_1^2)} \, e^{-2\pi i (\xi_0 u_0 + \xi_1 u_1)},$$ where the real Gaussian factor and the real linear form in the exponent are coerced into $\mathbb{C}$. The theorem asserts two things conjoined: first, that this function is integrable; second, that its integral equals $$(-i)^m\,(\xi_0 + \varepsilon i\,\xi_1)^m\, e^{-\pi(\xi_0^2+\xi_1^2)}.$$ Thus the Fourier transform (with the $e^{-2\pi i \langle \xi, u\rangle}$ normalisation) of the product of the harmonic homogeneous polynomial $(u_0 + \varepsilon i u_1)^m$ with the self-dual Gaussian $e^{-\pi|u|^2}$ is $(-i)^m$ times the same product evaluated at $\xi$. Only the two values $\varepsilon = \pm 1$ are allowed; no other hypothesis is imposed on $m$ or on $\xi$.
--
--   This is the two-dimensional case of the Hecke–Bochner identity: for $P$ harmonic and homogeneous of degree $m$, the function $P(u)e^{-\pi|u|^2}$ is an eigenfunction of the Fourier transform with eigenvalue $(-i)^m$, here for the polynomials $(u_0 \pm i u_1)^m$ that span the harmonic homogeneous polynomials of degree $m$ in two variables. It feeds the computation of the archimedean factors of Godement-type inner products against Gaussian test vectors and of the associated Mellin integrals in the cubic-induction construction of the relevant automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two
    (m : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (ξ : Fin 2 → ℝ) :
    Integrable (fun u : Fin 2 → ℝ =>
        (((u 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ m *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) ∧
    (∫ u : Fin 2 → ℝ,
        (((u 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ m *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ))))
      = (-Complex.I) ^ m * (((ξ 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((ξ 1 : ℝ) : ℂ)) ^ m *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ξ i ^ 2)) : ℂ) := by sorry
