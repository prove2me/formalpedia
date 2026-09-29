-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
-- name    : MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/c433f2e3-a7d3-5fe7-b1d1-53304ad66284
-- title:
--   Uniform bounds for a partial Fourier transform with one free slot
-- statement:
--   Fix natural numbers $n$ and $N$, an index $k \in \mathrm{Fin}(n+1)$ and a real $R \ge 0$. The assertion is the existence of a constant $K \ge 0$, depending only on these data, with the following property. Let $g : (\mathrm{Fin}(n+1) \to \mathbb{R}) \times \mathbb{R} \to \mathbb{C}$ be $C^\infty$ and suppose $g(p) = 0$ whenever some coordinate of the first component satisfies $R < |p_1(i)|$, i.e. $g$ vanishes off the box $[-R,R]^{n+1} \times \mathbb{R}$ in its first $n+1$ variables. Let $M$ be a real number bounding all iterated Fréchet derivatives of $g$ of order at most $N + 2n$: $\|D^i g(p)\| \le M$ for all $i \le N+2n$ and all $p$. Let $\xi' : \mathrm{Fin}(n) \to \mathbb{R}$, and define $h : \mathbb{R} \times \mathbb{R} \to \mathbb{C}$ by $h(q) = \int_{\mathbb{R}^n} g(\mathrm{Fin.insertNth}\ k\ q_1\ x', q_2)\, e^{-2\pi i \sum_{i} \xi'_i x'_i}\, dx'$, where $q_1$ is inserted into slot $k$ of $x'$. Then $h$ is $C^\infty$ on $\mathbb{R}^2$, $h(q) = 0$ whenever $R < |q_1|$, and for every $i \le N$ and every $q \in \mathbb{R}^2$ one has $\|D^i h(q)\| \le K\, M \prod_{i'} (1+|\xi'_{i'}|)^{-2}$. The constant $K$ is thus uniform in $g$, $M$ and $\xi'$, and the bound is linear in the $C^{N+2n}$ bound $M$.
--
--   This is the quantitative Schwartz-type decay estimate for a partial Fourier transform: integration over $n$ of the $n+2$ variables, with the slot-$k$ variable and the last variable left free, yields a smooth function of two variables whose derivatives up to order $N$ decay like $\prod (1+|\xi'_{i'}|)^{-2}$, uniformly in the transformed function. It feeds the companion statement [`MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod`](thm.html#MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod), where the integral over $\mathbb{R}^n$ is replaced by one over a bounded set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
    (n N : ℕ) (k : Fin (n + 1)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : (Fin (n + 1) → ℝ) × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ i, R < |p.1 i|) → g p = 0) →
      ∀ M : ℝ, (∀ i : ℕ, i ≤ N + 2 * n → ∀ p : (Fin (n + 1) → ℝ) × ℝ, ‖iteratedFDeriv ℝ i g p‖ ≤ M) →
      ∀ ξ' : Fin n → ℝ,
        let h : ℝ × ℝ → ℂ := fun q =>
          ∫ x' : Fin n → ℝ, g (Fin.insertNth k q.1 x', q.2) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ)))
        ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧
          ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
            ‖iteratedFDeriv ℝ i h q‖ ≤ K * M * ∏ i', (1 + |ξ' i'|)⁻¹ ^ 2 := by sorry
