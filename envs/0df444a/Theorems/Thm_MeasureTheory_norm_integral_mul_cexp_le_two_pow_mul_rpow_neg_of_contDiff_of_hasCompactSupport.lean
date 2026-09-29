-- Prove2me | Theorems.Thm_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
-- name    : MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/6bfa7dee-34b4-5970-86c2-a2094a52249e
-- title:
--   Non-stationary phase bound for oscillatory integrals on ℝ
-- statement:
--   Let $N$ be a natural number and let $H \colon \mathbb{R} \to \mathbb{C}$ be a function that is $N$ times continuously differentiable as a map of real vector spaces (in the sense of `ContDiff ℝ N H`) and has compact support. Then for every real number $l$ the oscillatory integral $\int_{\mathbb{R}} H(u)\, e^{i l u}\, du$, where the exponential is the complex exponential of $i \cdot l \cdot u$ and the integral is the Bochner integral with respect to Lebesgue measure on $\mathbb{R}$, satisfies
--   $$\Big\| \int_{\mathbb{R}} H(u)\, e^{i l u}\, du \Big\| \le 2^{N}\Big( \int_{\mathbb{R}} \|H(u)\|\, du + \int_{\mathbb{R}} \|H^{(N)}(u)\|\, du \Big)(1+|l|)^{-N},$$
--   where $H^{(N)}$ denotes the $N$-th iterated derivative of $H$, the two integrals on the right are the $L^1$ norms of $H$ and of $H^{(N)}$, and the final factor is the real power $(1+|l|)^{-(N:\mathbb{R})}$. The constant is thus explicit in terms of the $L^1$ norms of $H$ and its $N$-th derivative alone, and in particular is uniform over families of amplitudes with common bounds on these two quantities.
--
--   This is the one-dimensional non-stationary phase estimate: decay of order $(1+|l|)^{-N}$ for the Fourier transform of a compactly supported $C^N$ amplitude, with a constant depending only on the $L^1$ norms of $H$ and $H^{(N)}$. It is used in the archimedean analysis of automorphic forms, where the uniformity of the constant over families of amplitudes is what is needed to bound split-torus (Iwasawa) integrals and the associated spectral sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
    (N : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ N H) (hHc : HasCompactSupport H) (l : ℝ) :
    ‖∫ u : ℝ, H u * Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))‖
      ≤ 2 ^ N * ((∫ u : ℝ, ‖H u‖) + ∫ u : ℝ, ‖iteratedDeriv N H u‖) * (1 + |l|) ^ (-(N : ℝ)) := by sorry
