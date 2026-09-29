-- Prove2me | Theorems.Thm_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
-- name    : MeasureTheory.memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/01c4a974-5558-5672-8a80-3ce60d1f3e09
-- title:
--   L² bound for a polynomially bounded family from kernel-averaged pairings
-- statement:
--   Let $\iota$ be a finite type and let $\Theta_i\colon\mathbb R\to\mathbb C$, $i\in\iota$, be continuous functions, each of polynomial growth: for every $i$ there are $A\in\mathbb R$ and $k\in\mathbb N$ with $\|\Theta_i(t)\|\le A(1+|t|)^k$ for all $t$. Let $\rho\colon\mathbb R\to\mathbb R$ be measurable with $t\mapsto|t|^n\rho(t)$ integrable for every $n\in\mathbb N$ and $\int_{\mathbb R}\rho(t)\,dt=1$. Let $M\in\mathbb R$ and assume the following pairing bound: for every family $u_i\colon\mathbb R\to\mathbb C$ of measurable functions that vanish outside a common bounded set (there is $R$ with $u_i(x)=0$ whenever $R<|x|$, for all $i$) and are uniformly bounded (there is $B$ with $\|u_i(x)\|\le B$ for all $i,x$), and for every $\delta$ with $0<\delta\le1$, writing $v_i(t)=\int_{\mathbb R}u_i(x)\,\delta^{-1}\rho((t-x)/\delta)\,dx$, one has $\bigl\|\sum_i\int_{\mathbb R}\overline{v_i(t)}\,\Theta_i(t)\,dt\bigr\|\le M\bigl(\sum_i\int_{\mathbb R}\|v_i(t)\|^2\,dt\bigr)^{1/2}$. Then each $\Theta_i$ lies in $L^2$ of Lebesgue measure on $\mathbb R$, and $\sum_i\int_{\mathbb R}\|\Theta_i(t)\|^2\,dt\le M^2$.
--
--   This is the $L^2$ duality criterion in a scaled-kernel (approximate-identity) form: square-integrability with the sharp constant $M^2$ is deduced from bounds on pairings against $\rho_\delta$-averages of bounded, compactly supported test families, the kernel $\rho$ being allowed to change sign and entering only through its mass and its absolute moments. It is used in the analytic part of the treatment of automorphic forms, where the functions $\Theta_i$ arise as continuations along axes and the pairing bounds come from an integral estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
    {ι : Type} [Fintype ι] (Θ : ι → ℝ → ℂ) (hΘ : ∀ i, Continuous (Θ i))
    (hΘg : ∀ i, ∃ (A : ℝ) (k : ℕ), ∀ t, ‖Θ i t‖ ≤ A * (1 + |t|) ^ k)
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hρm : ∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t))
    (hρ1 : ∫ t : ℝ, ρ t = 1)
    (M : ℝ)
    (h : ∀ (u : ι → ℝ → ℂ), (∀ i, Measurable (u i)) →
      (∃ R : ℝ, ∀ i x, R < |x| → u i x = 0) → (∃ B : ℝ, ∀ i x, ‖u i x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖∑ i, ∫ t : ℝ, conj (∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) * Θ i t‖ ≤
        M * Real.sqrt (∑ i, ∫ t : ℝ, ‖∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)‖ ^ 2)) :
    (∀ i, MemLp (Θ i) 2) ∧ ∑ i, ∫ t : ℝ, ‖Θ i t‖ ^ 2 ≤ M ^ 2 := by sorry
