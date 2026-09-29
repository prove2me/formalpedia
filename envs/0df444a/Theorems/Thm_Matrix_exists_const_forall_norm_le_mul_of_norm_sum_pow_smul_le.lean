-- Prove2me | Theorems.Thm_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
-- name    : Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/79b8330a-0e70-5f29-87e5-67d1126dcfa7
-- title:
--   Uniform Vandermonde inversion bound for vector-valued coefficients
-- statement:
--   Let $L$ be a natural number and let $x : \mathrm{Fin}\,L \to \mathbb{C}$ be an injective family of complex numbers, i.e. $L$ pairwise distinct nodes $x_0,\dots,x_{L-1}$. The assertion is the existence of a real constant $C \ge 0$, depending only on $L$ and the nodes $x$, with the following uniform property: for every type $E$ carrying the structure of a normed additive commutative group and of a normed $\mathbb{C}$-vector space, for every family $v : \mathrm{Fin}\,L \to E$ and every real number $B$, if $\bigl\|\sum_{m<L} x_t^{\,m}\cdot v_m\bigr\| \le B$ holds for every index $t < L$, then $\|v_m\| \le C\,B$ for every index $m < L$. Note the order of quantifiers: the constant $C$ is chosen before the normed space $E$, the vectors $v_m$ and the bound $B$, so a single $C$ works for all complex Banach-space-valued coefficient families over the given nodes; no completeness of $E$ is required, and $B$ is not assumed non-negative in advance (its non-negativity follows from the hypothesis).
--
--   This is the quantitative form of the solvability of a Vandermonde system: at $L$ distinct nodes the coefficients of a vector-valued polynomial of degree $< L$ are bounded linearly in terms of its values, with a constant depending only on the nodes. It is used on the Langlands–Tunnell side of the argument, in the cubic-induction estimates [`LanglandsTunnell.CubicInduction.firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations`](thm.html#LanglandsTunnell.CubicInduction.firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations) and [`LanglandsTunnell.CubicInduction.secondRatioCoeff_flat_of_le_of_flat_of_casimir_relations`](thm.html#LanglandsTunnell.CubicInduction.secondRatioCoeff_flat_of_le_of_flat_of_casimir_relations), to transfer a uniform bound on values to a uniform bound on coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Vandermonde

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
    (L : ℕ) (x : Fin L → ℂ) (hx : Function.Injective x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (v : Fin L → E) (B : ℝ),
      (∀ t : Fin L, ‖∑ m : Fin L, (x t) ^ (m : ℕ) • v m‖ ≤ B) → ∀ m : Fin L, ‖v m‖ ≤ C * B := by sorry
