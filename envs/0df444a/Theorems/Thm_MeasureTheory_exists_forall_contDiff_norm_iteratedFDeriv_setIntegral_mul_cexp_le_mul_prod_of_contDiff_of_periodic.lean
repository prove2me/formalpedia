-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
-- name    : MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/1165fc52-4c17-5387-8df0-5f8ded26c417
-- title:
--   Uniform decay of angular Fourier modes of a smooth periodic window
-- statement:
--   Let $r,c$ be natural numbers and let $W \colon (\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,c \to \mathbb{R}) \to \mathbb{C}$ be smooth ($C^\infty$ in the real sense), let $R \ge 0$ be a real number, assume that $W(x,\theta) = 0$ whenever some coordinate of $x$ satisfies $|x_k| > R$, and assume that $W$ is invariant under translating the second argument by the standard basis vectors, i.e. $W(x, \theta + \mathrm{Pi.single}\,j\,1) = W(x,\theta)$ for all $(x,\theta)$ and all $j$. Then there exists a real $M \ge 0$ such that for every $m \colon \mathrm{Fin}\,c \to \mathbb{Z}$ the function
--   $$\Psi_m(x) \;=\; \int_{\theta \in \prod_j [0,1)} W(x,\theta)\, \exp\!\big(-2\pi i \textstyle\sum_j m_j \theta_j\big)\, d\theta$$
--   on $\mathrm{Fin}\,r \to \mathbb{R}$ is smooth; vanishes at every $x$ having a coordinate with $|x_k| > R$; and satisfies, for every $n \le 2r$ and every $x$, the bound $\|D^n \Psi_m(x)\| \le M \prod_j (1+|m_j|)^{-2}$ on the norm of the $n$-th iterated Fréchet derivative. The constant $M$ is independent of $m$, of $n \le 2r$ and of $x$.
--
--   This is the several-variable, parametrised form of the classical fact that the Fourier coefficients of a $C^k$ periodic function decay like $|m|^{-k}$, here with the decay holding simultaneously for all derivatives of order at most $2r$ in the parameter $x$ and with the support in $x$ preserved. It is used to show that the angular Fourier modes of a smooth periodic window form a summable family, as in the two results on summable families of product-Poisson windows that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : Fin c → ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) ∧
      (∀ x : Fin r → ℝ, (∃ k, R < |x k|) →
        (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) = 0) ∧
      ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ,
        ‖iteratedFDeriv ℝ n (fun x : Fin r → ℝ =>
            ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) x‖ ≤
          M * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 := by sorry
