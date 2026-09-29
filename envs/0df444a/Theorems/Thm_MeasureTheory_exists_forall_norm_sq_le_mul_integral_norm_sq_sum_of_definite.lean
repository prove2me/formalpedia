-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite
-- name    : MeasureTheory.exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/13051815-1045-54ce-9dd2-80dab4224857
-- title:
--   Coordinate domination by an L²-norm of a definite family
-- statement:
--   Let $X$ be a measurable space, $\mu$ a measure on $X$, $n$ a natural number and $b : \mathrm{Fin}\,n \to X \to \mathbb{C}$ a finite family of complex-valued functions on $X$. Assume first that all pairwise products are integrable: for all $i, j$, the function $x \mapsto b_i(x)\overline{b_j(x)}$ is $\mu$-integrable. Assume second that the associated quadratic form is definite on coefficient vectors: for every $a : \mathrm{Fin}\,n \to \mathbb{C}$, if $\int_X \bigl\| \sum_j a_j b_j(x) \bigr\|^2 \, d\mu(x) = 0$ then $a = 0$. The conclusion is the existence of a real constant $C > 0$ such that for every coefficient vector $a : \mathrm{Fin}\,n \to \mathbb{C}$ and every index $i$, $$\|a_i\|^2 \le C \int_X \Bigl\| \sum_j a_j b_j(x) \Bigr\|^2 \, d\mu(x).$$ Thus each coordinate of $a$ is dominated, uniformly in $a$ and $i$, by the integral of the squared norm of the corresponding combination of the $b_j$. The constant is uniform in $a$ but of course depends on $\mu$ and on the family $b$.
--
--   This is the standard equivalence-of-norms statement for a finite family of functions that is linearly independent modulo $\mu$-null functions: the sup-norm of the coefficient vector is controlled by the $L^2(\mu)$-norm of the combination. It serves as the measure-theoretic input to the coordinate-domination step used in [`AutomorphicForm.exists_basis_forall_flat_isInducedSection_family_eq_sum_and_norm_sq_le_lintegral_of_principalLevel_archCutSubmodule`](thm.html#AutomorphicForm.exists_basis_forall_flat_isInducedSection_family_eq_sum_and_norm_sq_le_lintegral_of_principalLevel_archCutSubmodule), where sections induced from a principal level structure are expanded in a finite basis with integral bounds on the coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (b : Fin n → X → ℂ)
    (hint : ∀ i j : Fin n, Integrable (fun x => b i x * conj (b j x)) μ)
    (hdef : ∀ a : Fin n → ℂ, (∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ) = 0 → a = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℂ) (i : Fin n), ‖a i‖ ^ 2 ≤ C * ∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ := by sorry
