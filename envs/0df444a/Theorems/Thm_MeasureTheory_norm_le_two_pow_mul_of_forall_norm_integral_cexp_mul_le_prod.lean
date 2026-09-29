-- Prove2me | Theorems.Thm_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
-- name    : MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/d23ba4ca-61aa-5045-8e90-6a61a2f54af8
-- title:
--   Sup bound from product decay of the Fourier transform
-- statement:
--   Let $r$ be a natural number and let $f : \mathbb{R}^r \to \mathbb{C}$, with $\mathbb{R}^r$ realised as functions $\mathrm{Fin}\,r \to \mathbb{R}$ with the product (Lebesgue) measure, be continuous and integrable. Let $C$ be a real number and suppose that for every $\xi : \mathrm{Fin}\,r \to \mathbb{R}$ the Fourier integral, written with the explicit character, satisfies $$\Bigl\| \int_{\mathbb{R}^r} \exp\bigl(-2\pi i \textstyle\sum_k \xi_k x_k\bigr) f(x)\,dx \Bigr\| \le C \prod_{k} (1 + |\xi_k|)^{-2}.$$ Then for every $x : \mathrm{Fin}\,r \to \mathbb{R}$ one has $\|f(x)\| \le 2^r C$. The hypothesis is thus a pointwise bound on the Fourier transform of $f$ by $C$ times a product of one-dimensional weights, and the conclusion is a uniform bound on $f$ itself by $2^r C$, the factor $2^r$ being the total integral of that product weight over $\mathbb{R}^r$.
--
--   This is the standard sup-norm estimate obtained from Fourier inversion when the Fourier transform is dominated by an integrable function: the sup norm of $f$ is at most the $L^1$ norm of the dominating function. It is used in the construction of summable bounds on the Fourier modes of periodic smooth windows, where a bound on the $\xi$-side is converted into a bound on the $x$-side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
    {r : ℕ} (f : (Fin r → ℝ) → ℂ) (hf : Continuous f) (hfi : Integrable f) (C : ℝ)
    (hC : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x‖ ≤ C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
    (x : Fin r → ℝ) :
    ‖f x‖ ≤ 2 ^ r * C := by sorry
