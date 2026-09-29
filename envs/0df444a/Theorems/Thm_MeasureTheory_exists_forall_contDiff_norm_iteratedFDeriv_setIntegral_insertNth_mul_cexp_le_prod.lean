-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod
-- name    : MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2bdd79a1-f232-5db8-a6d6-3c44e4610be5
-- title:
--   Uniform decay of partial angular Fourier modes, one angle free
-- statement:
--   Let $n,d$ be natural numbers and let $W\colon(\mathbb{R}^{n+1})\times(\mathbb{R}^{d+1})\to\mathbb{C}$ be smooth (`ContDiff ℝ ⊤`). Let $R\ge 0$ and assume that $W(x,\theta)=0$ whenever $|x_k|>R$ for some coordinate $k$, and that $W$ is invariant under each unit shift in the angular variables: $W(x,\theta+\mathrm{e}_j)=W(x,\theta)$ for every $j\in\mathrm{Fin}(d+1)$, where $\mathrm{e}_j$ is `Pi.single j 1`. Fix an angular slot $j\in\mathrm{Fin}(d+1)$ and an order $N\in\mathbb{N}$. Then there exists $M\ge 0$ such that for every $m'\colon \mathrm{Fin}\,d\to\mathbb{Z}$ the function
--   $$g(x,t)=\int_{[0,1)^{d}} W\bigl(x,\mathrm{insertNth}_j\,t\,\theta'\bigr)\,\exp\bigl(-2\pi i\textstyle\sum_{j'} m'_{j'}\theta'_{j'}\bigr)\,d\theta',$$
--   the integral being taken over the product of the intervals $[0,1)$ and $\mathrm{insertNth}_j\,t\,\theta'\in\mathbb{R}^{d+1}$ denoting $\theta'$ with $t$ inserted in slot $j$, satisfies: $g$ is smooth on $(\mathbb{R}^{n+1})\times\mathbb{R}$; $g(x,t)=0$ whenever $|x_k|>R$ for some $k$; $g(x,t+1)=g(x,t)$; and for every $i\le N$ and every $(x,t)$,
--   $$\|D^i g(x,t)\|\le M\prod_{j'}\bigl(1+|m'_{j'}|\bigr)^{-2}.$$
--   The constant $M$ is independent of $m'$.
--
--   This is the quantitative smoothness-plus-decay statement for the partial Fourier transform of a smooth, box-supported, $\mathbb{Z}^{d+1}$-periodic window in all but one of its angular variables: differentiating under the integral gives smoothness, while integration by parts in the integrated angles gives the quadratic decay in the dual variables $m'$, uniformly in $m'$. It feeds the two-variable version [`MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod`](thm.html#MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod), where the remaining free angle is also transformed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m' : Fin d → ℤ,
      let g : (Fin (n + 1) → ℝ) × ℝ → ℂ := fun p =>
        ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (p.1, Fin.insertNth j p.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ k, R < |p.1 k|) → g p = 0) ∧
        (∀ p : (Fin (n + 1) → ℝ) × ℝ, g (p.1, p.2 + 1) = g p) ∧
        ∀ i : ℕ, i ≤ N → ∀ p : (Fin (n + 1) → ℝ) × ℝ,
          ‖iteratedFDeriv ℝ i g p‖ ≤ M * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := by sorry
