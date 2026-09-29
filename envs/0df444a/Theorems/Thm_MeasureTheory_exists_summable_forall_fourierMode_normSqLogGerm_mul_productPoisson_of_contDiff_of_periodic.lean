-- Prove2me | Theorems.Thm_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
-- name    : MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/c2c4d59a-d6e2-5f4f-a79b-2f957ae9ed8c
-- title:
--   Summable Fourier modes of a logarithmic complex-place germ window
-- statement:
--   Fix natural numbers $r,c$ and a function $W\colon(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,c\to\mathbb R)\to\mathbb C$ that is $C^\infty$ on $\mathbb R^{r}\times\mathbb R^{c}$, and let $R\ge 0$ be such that $W(x,\theta)=0$ as soon as $|x_i|>R$ for some coordinate $i$, and such that $W(x,\theta+e_{j'})=W(x,\theta)$ for every $\theta$ and every angular index $j'$ (translation by the standard basis vector $\mathrm{Pi.single}\,j'\,1$). Fix indices $k$ among the real slots and $j$ among the angular slots (so $r,c\ge 1$). For $m\in\mathbb Z^{c}$ define $$\Psi_m(x)=\int_{[0,1)^{c}}\bigl\|1-e^{x_k/2+2\pi i\theta_j}\bigr\|^{2}\log\bigl\|1-e^{x_k/2+2\pi i\theta_j}\bigr\|\;W(x,\theta)\,e^{-2\pi i\sum_{j'}m_{j'}\theta_{j'}}\,d\theta,$$ the real germ factor being viewed in $\mathbb C$. The assertion is that there exist reals $C_m\ge 0$, indexed by $m\in\mathbb Z^{c}$, with $\sum_m C_m$ summable, such that for every $m$ the function $\Psi_m$ on $\mathbb R^{r}$ is continuous and integrable and satisfies both $\|\Psi_m(x)\|\le C_m\prod_i(1+|x_i|)^{-2}$ for all $x$, and $\bigl\|\int_{\mathbb R^r}e^{-2\pi i\sum_i\xi_i x_i}\Psi_m(x)\,dx\bigr\|\le C_m\prod_i(1+|\xi_i|)^{-2}$ for all $\xi$.
--
--   This is the complex-place contribution to a Poisson-summation estimate: the smooth periodic window multiplied by the germ $|1-e^{s/2+2\pi i t}|^{2}\log|1-e^{s/2+2\pi i t}|$ is expanded into Fourier modes in the angular variables, and each mode is shown to be a window on $\mathbb R^{r}$ with product decay of order $2$ both in space and in frequency, with mode constants forming a summable family. It feeds [`MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson`](thm.html#MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin r) (j : Fin c) :
    let Ψ : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        ((‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) *
            W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m j' : ℝ) * θ j' : ℝ) : ℂ)))
    ∃ C : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ C m) ∧ Summable C ∧
      ∀ m : Fin c → ℤ, Continuous (Ψ m) ∧ Integrable (Ψ m) ∧
        (∀ x : Fin r → ℝ, ‖Ψ m x‖ ≤ C m * ∏ i, (1 + |x i|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ m x‖ ≤
            C m * ∏ i, (1 + |ξ i|)⁻¹ ^ 2) := by sorry
