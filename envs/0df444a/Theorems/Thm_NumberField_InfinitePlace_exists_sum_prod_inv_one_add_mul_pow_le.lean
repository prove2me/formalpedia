-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le
-- name    : NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/f6df9715-4807-559b-b460-4420c94dba82
-- title:
--   Uniform decay of lattice sums over s⁻¹𝒪_F
-- statement:
--   Let $F$ be a number field, let $s$ be a non-zero element of its ring of integers $\mathcal{O}_F$, and let $N$ be a natural number. The assertion is that there exist a natural number $M$ and a real constant $C \ge 0$ with the following property. Let $y$ be any family of real numbers indexed by the infinite places $w$ of $F$ such that $y_w > 0$ for every $w$ and such that $Y := \prod_w y_w^{m_w} \ge 1$, where $m_w$ denotes the multiplicity of $w$ (its local degree, $1$ at a real place and $2$ at a complex place). Let $T$ be any finite subset of $F$ all of whose elements $\xi$ are non-zero and satisfy $s\xi \in \mathcal{O}_F$, i.e. $s\xi$ is the image in $F$ of some element of $\mathcal{O}_F$. Then
--   $$\sum_{\xi \in T} \prod_{w} \bigl(1 + y_w\, w(\xi)\bigr)^{-M} \le C\, Y^{-N},$$
--   the product being over all infinite places and $w(\xi)$ the value of the place $w$ at $\xi$. Thus $M$ and $C$ depend only on $F$, $s$ and $N$, and in particular not on the individual sizes of the $y_w$ beyond the normalisation $Y \ge 1$, nor on $T$.
--
--   This is a geometry-of-numbers estimate: sums of the displayed shape over the non-zero elements of the fractional ideal $s^{-1}\mathcal{O}_F$ decay like a fixed negative power of the archimedean height $Y = \prod_w y_w^{m_w}$, uniformly in how the weights $y_w$ are distributed among the infinite places, the uniformity coming from Dirichlet's unit theorem in the form [`NumberField.Units.exists_forall_abs_sub_mult_mul_log_le`](thm.html#NumberField.Units.exists_forall_abs_sub_mult_mul_log_le). Since the bound is stated for arbitrary finite subsets $T$ and the terms are non-negative, summability over the whole fractional ideal with the same bound follows; it is used to control the non-trivial Fourier modes in the bounds for automorphic forms on $\mathrm{GL}_2$, namely [`AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact`](thm.html#AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact) and [`AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn`](thm.html#AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le.lean

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le
    (F : Type) [Field F] [NumberField F] {s : NumberField.RingOfIntegers F} (hs : s ≠ 0) (N : ℕ) :
    ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : NumberField.InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      1 ≤ ∏ w, y w ^ w.mult →
      ∀ T : Finset F,
        (∀ ξ ∈ T, ξ ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers F, (a : F) = (s : F) * ξ) →
        ∑ ξ ∈ T, ∏ w : NumberField.InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
          ≤ C * ((∏ w : NumberField.InfinitePlace F, y w ^ w.mult) ^ N)⁻¹ := by sorry
