-- Prove2me | Theorems.Thm_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
-- name    : LocalParametrix.exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a6af2354-ee6b-5be2-9ea2-a29e7ef8b0b3
-- title:
--   Parametrix symbol of order -2m for an elliptic frequency-side operator
-- statement:
--   Let $V$ be a finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra and the associated Lebesgue (Haar) measure, let $\iota$ be a finite index type, let $B_i \colon V \to V$ ($i \in \iota$) be continuous linear endomorphisms, and let $v_i \in V$ be vectors whose range spans $V$ as a real subspace, i.e. $\operatorname{span}_{\mathbb R}\{v_i\} = V$. Let $m$ be a natural number with $\dim_{\mathbb R} V < 2m$. Consider the operator on functions $g \colon V \to \mathbb C$ given by
--   $$(\mathcal P g)(\eta) = \sum_i \Big[ D^2 g(\eta)\big(B_i^{*}\eta, B_i^{*}\eta\big) + 4\pi i \,\langle \eta, v_i\rangle\, Dg(\eta)\big(B_i^{*}\eta\big) - 4\pi^2 \langle \eta, v_i\rangle^2 g(\eta)\Big],$$
--   where $B_i^{*}$ is the adjoint of $B_i$, the second derivative is evaluated at the constant family with both arguments equal to $B_i^{*}\eta$, and $\langle\cdot,\cdot\rangle$ is the real inner product, viewed in $\mathbb C$. The assertion is that there exists $r \colon V \to \mathbb C$ which is infinitely differentiable in the real sense, satisfies symbol estimates of order $-2m$, namely for every $n \in \mathbb N$ there is a constant $C$ with $\|D^n r(\xi)\| \le C(1+\|\xi\|)^{-(2m+n)}$ for all $\xi \in V$, and is such that the function $\xi \mapsto (\mathcal P^{m} r)(\xi) - 1$, with $\mathcal P^{m}$ the $m$-th iterate of $\mathcal P$, is integrable on $V$.
--
--   This is Hörmander's asymptotic inversion of an elliptic symbol made explicit for the frequency-side operator attached to the affine vector fields $y \mapsto B_i y + v_i$: the spanning hypothesis on the $v_i$ makes $Q(\xi) = \sum_i \langle \xi, v_i\rangle^2$ positive definite, so the top-order part of $\mathcal P$ is multiplication by $-4\pi^2 Q(\xi)$, and the condition $\dim_{\mathbb R} V < 2m$ makes a symbol of order $-2m$ integrable. It is used in the construction of an integral representation for functions in terms of iterated derivatives along the fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

theorem LocalParametrix.exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)
    (hv : Submodule.span ℝ (Set.range v) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ r : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ))) ∧
      Integrable (fun ξ : V => ((fun (g : V → ℂ) (η : V) => ∑ i,
          (iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) +
            (4 * Real.pi * Complex.I) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
              fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η) -
            (4 * Real.pi ^ 2 : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2 * g η))^[m] r) ξ - 1) := by sorry
