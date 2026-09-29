-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod
-- name    : MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2e926138-d80b-5ba7-a457-818384aff554
-- title:
--   Mixed partial Fourier transform: smoothness and quadratic decay
-- statement:
--   Let $n,d$ be natural numbers and let $W:(\mathrm{Fin}(n+1)\to\mathbb R)\times(\mathrm{Fin}(d+1)\to\mathbb R)\to\mathbb C$ be smooth ($C^\infty$ over $\mathbb R$). Let $R\ge 0$ and assume the support hypothesis that $W(p)=0$ whenever $|p_1(k)|>R$ for some index $k$, and the periodicity hypothesis that $W(p_1,p_2+\delta_j)=W(p_1,p_2)$ for every $p$ and every angular index $j$, where $\delta_j$ is the standard basis vector $\mathtt{Pi.single}\ j\ 1$. Fix $k\in\mathrm{Fin}(n+1)$, $j\in\mathrm{Fin}(d+1)$ and $N\in\mathbb N$. Then there is a constant $M\ge 0$, independent of the frequencies, such that for every $\xi'\colon\mathrm{Fin}\,n\to\mathbb R$ and every $m'\colon\mathrm{Fin}\,d\to\mathbb Z$ the function $h:\mathbb R\times\mathbb R\to\mathbb C$,
--   $$h(q)=\int_{\mathbb R^{n}}\ \int_{[0,1)^{d}} W\bigl(\mathtt{Fin.insertNth}\,k\,q_1\,x',\ \mathtt{Fin.insertNth}\,j\,q_2\,\theta'\bigr)\,e^{-2\pi i\sum_i \xi'_i x'_i}\,e^{-2\pi i\sum_{j'} m'_{j'}\theta'_{j'}}\,d\theta'\,dx',$$
--   the inner integral being taken over the product set $\prod_{j'}[0,1)$ and the outer over $\mathbb R^{n}$, satisfies: $h$ is smooth; $h(q)=0$ whenever $|q_1|>R$; $h(q_1,q_2+1)=h(q_1,q_2)$ for all $q$; and $\|\mathrm{iteratedFDeriv}_{\mathbb R}^{\,i}h(q)\|\le M\bigl(\prod_{i'}(1+|\xi'_{i'}|)^{-2}\bigr)\prod_{j'}(1+|m'_{j'}|)^{-2}$ for all $i\le N$ and all $q\in\mathbb R\times\mathbb R$.
--
--   This is the joint smoothness-and-decay estimate for a window that has been partially Fourier-analysed in all but one Euclidean variable (slot $k$) and all but one angular variable (slot $j$): the remaining two-variable function retains the support and periodicity properties of $W$ and its derivatives up to order $N$ decay quadratically in each frequency. It supplies the regularity input for [`MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic`](thm.html#MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic), where the product decay makes the double sum over $(\xi',m')$-type modes summable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin (n + 1)) (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ξ' : Fin n → ℝ) (m' : Fin d → ℤ),
      let h : ℝ × ℝ → ℂ := fun q =>
        ∫ x' : Fin n → ℝ, ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (Fin.insertNth k q.1 x', Fin.insertNth j q.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧ (∀ q : ℝ × ℝ, h (q.1, q.2 + 1) = h q) ∧
        ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
          ‖iteratedFDeriv ℝ i h q‖ ≤ M * (∏ i', (1 + |ξ' i'|)⁻¹ ^ 2) * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := by sorry
