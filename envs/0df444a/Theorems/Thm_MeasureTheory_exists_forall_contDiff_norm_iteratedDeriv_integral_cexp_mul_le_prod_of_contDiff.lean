-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff
-- name    : MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/96988971-a9a7-5471-8e64-20afe36749a5
-- title:
--   Uniform C² bounds for a partial Fourier transform
-- statement:
--   Fix $n \in \mathbb{N}$ and a real $R \ge 0$. The assertion is that there exists a constant $K \ge 0$, depending only on $n$ and $R$, with the following property. Let $h : \mathbb{R} \times (\mathrm{Fin}\,n \to \mathbb{R}) \to \mathbb{C}$ be smooth (of class $C^\infty$ over $\mathbb{R}$), vanishing at every point $p$ with $R < |p_1|$ and at every point $p$ whose second coordinate has some entry $p_2(k)$ with $R < |p_2(k)|$; let $M$ be a real number such that $\|\mathrm{iteratedFDeriv}\,\mathbb{R}\,N\,h\,p\| \le M$ for all orders $N \le 2n + 2$ and all points $p$. Then for every frequency $\xi : \mathrm{Fin}\,n \to \mathbb{R}$ the partial transform $H(x) = \int_{\mathbb{R}^n} h(x,y)\,e^{-2\pi i \sum_k \xi_k y_k}\,dy$ satisfies three things: $H$ is of class $C^2$ on $\mathbb{R}$; $H(x) = 0$ whenever $R < |x|$; and for every $j \le 2$ and every $x \in \mathbb{R}$, $\|\mathrm{iteratedDeriv}\,j\,H\,x\| \le K \cdot M \cdot \prod_k (1 + |\xi_k|)^{-2}$. Note that $K$ is chosen before $h$, $M$ and $\xi$, so the bound is uniform in all of them.
--
--   This is the standard rapid-decay estimate for a Fourier transform taken in part of the variables: smoothness and compact support in the $y$-variables give decay $\prod_k(1+|\xi_k|)^{-2}$ in the dual variables, with constants uniform over all data bounded by $M$, while differentiation under the integral sign gives two derivatives in the remaining variable $x$. It is used in assembling the summability and mode-by-mode bounds for a tensorised Poisson-summation argument, via [`MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic`](thm.html#MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ p : ℝ × (Fin n → ℝ), R < |p.1| → h p = 0) → (∀ p : ℝ × (Fin n → ℝ), (∃ k, R < |p.2 k|) → h p = 0) →
      ∀ M : ℝ, (∀ N : ℕ, N ≤ 2 * n + 2 → ∀ p : ℝ × (Fin n → ℝ), ‖iteratedFDeriv ℝ N h p‖ ≤ M) →
      ∀ ξ : Fin n → ℝ,
        ContDiff ℝ 2 (fun x : ℝ =>
          ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) ∧
        (∀ x : ℝ, R < |x| →
          (∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) = 0) ∧
        ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
          ‖iteratedDeriv j (fun x : ℝ =>
              ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) x‖ ≤
            K * M * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by sorry
