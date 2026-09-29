-- Prove2me | Theorems.Thm_MeasureTheory_exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic
-- name    : MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0ada5295-0822-557d-8c9e-8be90cb6444e
-- title:
--   Summable Fourier modes of a kink-weighted periodic window
-- statement:
--   Fix natural numbers $r$ and $c$, a function $W\colon(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,c\to\mathbb R)\to\mathbb C$ which is $C^\infty$ over $\mathbb R$, and a real $R\ge 0$ such that $W(x,\theta)=0$ whenever $|x_k|>R$ for some coordinate $k$, and such that $W(x,\theta+e_j)=W(x,\theta)$ for every $j\in\mathrm{Fin}\,c$, where $e_j$ is the $j$-th standard basis vector (`Pi.single j 1`); fix also an index $k\in\mathrm{Fin}\,r$. For $m\in\mathbb Z^c$ let $$\Psi_m(x)=\int_{[0,1)^c}\bigl|1-e^{x_k}\bigr|\,W(x,\theta)\,e^{-2\pi i\sum_{j}m_j\theta_j}\,d\theta,$$ the factor $|1-\exp(x_k)|$ being a real absolute value viewed in $\mathbb C$ and the integral taken over the product of the intervals $[0,1)$. The assertion is that there is a function $C\colon\mathbb Z^c\to\mathbb R$ with $C_m\ge 0$ for all $m$ and $\sum_m C_m$ convergent, such that for every $m\in\mathbb Z^c$ the function $\Psi_m$ on $\mathbb R^r$ is continuous, integrable for the volume measure, satisfies $\|\Psi_m(x)\|\le C_m\prod_i(1+|x_i|)^{-2}$ for all $x$, and satisfies $\bigl\|\int_{\mathbb R^r}e^{-2\pi i\sum_i\xi_i x_i}\Psi_m(x)\,dx\bigr\|\le C_m\prod_i(1+|\xi_i|)^{-2}$ for all $\xi\in\mathbb R^r$.
--
--   This is the real-place contribution, weighted by the non-smooth factor $|1-e^{x_k}|$, to a Poisson-summation estimate: each Fourier mode in the periodic variables is a window whose size and Fourier transform both decay like $\prod_i(1+|\cdot_i|)^{-2}$, with constants summable over the modes, which is exactly the input needed for absolutely convergent Poisson summation over a lattice. It is used by [`MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson`](thm.html#MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin r) :
    let Ψ : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        ((|1 - Real.exp (x k)| : ℝ) : ℂ) * W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m j' : ℝ) * θ j' : ℝ) : ℂ)))
    ∃ C : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ C m) ∧ Summable C ∧
      ∀ m : Fin c → ℤ, Continuous (Ψ m) ∧ Integrable (Ψ m) ∧
        (∀ x : Fin r → ℝ, ‖Ψ m x‖ ≤ C m * ∏ i, (1 + |x i|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ m x‖ ≤
            C m * ∏ i, (1 + |ξ i|)⁻¹ ^ 2) := by sorry
