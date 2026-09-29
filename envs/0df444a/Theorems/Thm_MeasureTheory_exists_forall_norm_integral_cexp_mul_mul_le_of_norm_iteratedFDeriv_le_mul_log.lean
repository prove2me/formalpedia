-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
-- name    : MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/6b3df5b6-8382-5dd3-9788-741206434297
-- title:
--   Fourier decay for a C⁴ window times a logarithmic degree-two singularity
-- statement:
--   Fix a real $r>0$. The assertion is that there exists a constant $C\ge 0$, depending only on $r$, such that the following holds for all data: for every function $G:\mathbb{R}\times\mathbb{R}\to\mathbb{R}$, every function $H:\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ and all reals $A,B\ge 0$ subject to the hypotheses that $G$ is $C^4$ on the set of $p\neq 0$ and satisfies, for every order $n\le 4$ and every $p\neq 0$ with $\|p\|\le r$, the bound $\|p\|^n\,\|D^nG(p)\|\le A\,\|p\|^2\,(1+|\log\|p\||)$ on the $n$-th iterated Fréchet derivative, and that $H$ is $C^4$ on all of $\mathbb{R}\times\mathbb{R}$, vanishes at every $p$ with $r\le\|p\|$, and has $\|D^nH(p)\|\le B$ for all $n\le 4$ and all $p$; then for all real $\xi,\eta$, $$\Bigl\|\int_{\mathbb{R}\times\mathbb{R}} e^{-2\pi i(\xi p_1+\eta p_2)}\,G(p)\,H(p)\,dp\Bigr\| \le C\,A\,B\,\bigl((1+|\xi|+|\eta|)^{7/2}\bigr)^{-1},$$ the integral being taken against the volume measure on $\mathbb{R}\times\mathbb{R}$ and the exponent $7/2$ a real power. Here $\|p\|$ is the norm of the product $\mathbb{R}\times\mathbb{R}$, namely $\max(|p_1|,|p_2|)$.
--
--   This is the standard decay estimate for the two-dimensional Fourier transform of a compactly supported function whose only singularity is of logarithmically homogeneous type of degree two at the origin; the exponent $7/2$ is weaker than the sharp rate $|\zeta|^{-4}\log|\zeta|$ but avoids logarithmic factors. It is used by [`MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le`](thm.html#MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le) to bound the mixed Fourier integral of a germ of the form (smooth function) times $s\log s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
        ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0} →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
            ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) →
        ContDiff ℝ 4 H → (∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0) →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B) →
        ∀ ξ η : ℝ,
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ))) *
              ((G p : ℂ) * H p)‖ ≤
            C * A * B * ((1 + |ξ| + |η|) ^ (7 / 2 : ℝ))⁻¹ := by sorry
