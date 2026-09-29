-- Prove2me | Theorems.Thm_IsNonarchimedean_abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one
-- name    : IsNonarchimedean.abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/1a6316d1-f519-5496-b62f-5309730b0654
-- title:
--   Unit coordinates are preserved by small Plücker minors
-- statement:
--   Let $K$ be a field and $\mu : K \to \mathbb{R}$ an absolute value which is non-archimedean, i.e. $\mu(a+b) \le \max(\mu(a),\mu(b))$ for all $a,b$. Fix a natural number $r$ and two vectors $x, v : \mathrm{Fin}\,r \to K$ subject to: $\mu(x_l) \le 1$ for every index $l$; $\mu(v_l) \le 1$ for every index $l$; there exists an index $j$ with $\mu(v_j) = 1$; and the supremum of $\mu(x_{l}v_{m} - x_{m}v_{l})$ over all ordered pairs $(l,m) \in \mathrm{Fin}\,r \times \mathrm{Fin}\,r$ of indices is strictly less than $1$ (the supremum being taken in $\mathbb{R}$, over a finite, hence bounded, index set). Then for every index $i$ such that $\mu(x_i) = 1$ one has $\mu(v_i) = 1$. In words: if the $2\times 2$ minors of the matrix with rows $x$ and $v$ are all of absolute value $<1$, and both rows are integral with $v$ having at least one coordinate of absolute value $1$, then every coordinate position at which $x$ attains absolute value $1$ is also a position at which $v$ attains absolute value $1$.
--
--   This is the pivot-stability statement for the non-archimedean chordal metric on projective space: two integral representatives whose Plücker minors are all small have the same set of coordinates of absolute value one, so a single affine chart serves a whole chordal ball of radius less than $1$. It is used in the analysis of points on the modular curve $J_0$, where it supplies charts around a point and comparisons of absolute values of evaluations at nearby points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsNonarchimedean_abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem IsNonarchimedean.abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) (hv1 : ∃ j, μ (v j) = 1)
    (hlt : (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) < 1)
    (i : Fin r) (hi : μ (x i) = 1) : μ (v i) = 1 := by sorry
