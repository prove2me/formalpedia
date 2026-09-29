-- Prove2me | Theorems.Thm_ModularForm_heckeU_add_slash_fricke_eq_zero
-- name    : ModularForm.heckeU_add_slash_fricke_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/b190be87-41d3-584b-a820-5903af954342
-- title:
--   Fricke matrix acts as -Uₚ in weight two
-- statement:
--   Let $p$ be a prime and let $f$ be a holomorphic modular form of weight $2$ for the congruence subgroup $\Gamma_0(p)$, regarded via its underlying function on the upper half-plane. Let $W$ be an element of the general linear group $\mathrm{GL}_2(\mathbb{R})$ whose underlying matrix is $\begin{pmatrix} 0 & -1 \\ p & 0 \end{pmatrix}$, the Fricke matrix of level $p$. The assertion is an identity of functions on the upper half-plane: the sum $\sum_{j=0}^{p-1} f \mid_2 \begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix}$, which is the operator [`ModularForm.heckeU`](def/ModularForm_HeckeOperator.html#L93) in weight $2$ at $p$ (defined as the sum over $j$ in the range $p$ of the weight-$k$ slash of $f$ by the matrices `heckeMatrix p j`, the upper triangular matrices with diagonal entries $1, p$ and upper right entry $j$, the case $p = 0$ being replaced by the identity matrix), added to $f \mid_2 W$, is the zero function. Here $\mid_2$ denotes Mathlib's weight-$2$ slash action of $\mathrm{GL}_2(\mathbb{R})$ on functions on the upper half-plane. Equivalently, $f \mid_2 W = -U_p f$.
--
--   This is the prime-level Atkin–Lehner relation between the Fricke matrix and the operator $U_p$ in weight two; in terms of $q$-expansions it says that the expansion of $f$ at the cusp $0$ is $-\sum_n a_{np}(f) q^n$. It is used in the weight-two constant-term arguments that compare forms on $\Gamma_0(p)$ with level-one data, namely in [`ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two`](thm.html#ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two) and [`ModularForm.exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two`](thm.html#ModularForm.exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_add_slash_fricke_eq_zero.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm MatrixGroups

theorem ModularForm.heckeU_add_slash_fricke_eq_zero (p : ℕ) [Fact p.Prime]
    (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0 := by sorry
