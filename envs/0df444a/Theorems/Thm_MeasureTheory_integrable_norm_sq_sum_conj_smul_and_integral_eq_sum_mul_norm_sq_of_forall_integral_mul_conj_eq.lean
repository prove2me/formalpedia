-- Prove2me | Theorems.Thm_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
-- name    : MeasureTheory.integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/6e64ae13-19b4-563f-b342-7c0b17d80e23
-- title:
--   Finite Parseval identity for vector-valued L² expansions
-- statement:
--   Let $X$ be a measurable space with a measure $\rho$, let $E$ be a complex inner product space (a normed additive commutative group with a compatible $\mathbb{C}$-inner product), and let $J$ be a finite index set with decidable equality. Let $\varphi : J \to X \to \mathbb{C}$ be a family of functions such that each $\varphi_j$ lies in $L^2(\rho)$, in the sense of Mathlib's `MemLp (φ j) 2 ρ`, let $v : J \to E$ be a family of vectors, and let $s : J \to \mathbb{R}$ be real numbers. Assume the orthogonality relations: for all $j, j' \in J$, $\int_X \varphi_j(x)\,\overline{\varphi_{j'}(x)}\,d\rho(x)$ equals the complex number $s_j$ when $j = j'$ and $0$ otherwise. The conclusion is the conjunction of two assertions: first, the real-valued function $x \mapsto \bigl\|\sum_{j} \overline{\varphi_j(x)} \cdot v_j\bigr\|^2$ is $\rho$-integrable; second, its integral equals $\sum_{j} s_j \|v_j\|^2$. Here the sums are over all of $J$, the scalar action is that of $\mathbb{C}$ on $E$, and no completeness or separability hypothesis on $E$, nor any $\sigma$-finiteness hypothesis on $\rho$, is imposed.
--
--   This is the finite Parseval identity for an $E$-valued function expanded along a finite orthogonal system of square-integrable scalar functions, with the normalisations $s_j$ of the system left arbitrary rather than set to $1$. It serves to evaluate Hilbert–Schmidt-type integrals $\int \|\sum_j \overline{\varphi_j(x)} v_j\|^2\,d\rho$ arising from smoothed reproducing vectors of a finite-dimensional space of cusp forms, and is used in the analysis of convolution operators on a fundamental domain for a principal level subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
    {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Type*} [Fintype J] [DecidableEq J]
    (φ : J → X → ℂ) (hφ : ∀ j, MemLp (φ j) 2 ρ) (v : J → E) (s : J → ℝ)
    (horth : ∀ j j', ∫ x, φ j x * conj (φ j' x) ∂ρ = if j = j' then ((s j : ℝ) : ℂ) else 0) :
    Integrable (fun x => ‖∑ j, conj (φ j x) • v j‖ ^ 2) ρ ∧
      ∫ x, ‖∑ j, conj (φ j x) • v j‖ ^ 2 ∂ρ = ∑ j, s j * ‖v j‖ ^ 2 := by sorry
