-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
-- name    : Matrix.SpecialLinearGroup.exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/8bc8134e-f99c-5b41-9c9c-7ac024bbd5f4
-- title:
--   Unit scalars on primitive vectors of (ℤ/m)² come from SL₂(ℤ)
-- statement:
--   Let $m$ be a natural number, assumed nonzero, let $w = (w_1, w_2)$ be a pair of elements of $\mathbb Z/m$ whose additive order in the group $\mathbb Z/m \times \mathbb Z/m$ is exactly $m$, and let $a$ be a unit of $\mathbb Z/m$. The assertion is that there exists a matrix $\gamma \in \mathrm{SL}_2(\mathbb Z)$ such that, after reducing its entries modulo $m$, the resulting matrix sends the column vector $w$ to $a\,w$; explicitly, the two stated equalities in $\mathbb Z/m$ are $\overline{\gamma_{00}} w_1 + \overline{\gamma_{01}} w_2 = a\, w_1$ and $\overline{\gamma_{10}} w_1 + \overline{\gamma_{11}} w_2 = a\, w_2$, where $\overline{(\cdot)}$ denotes the image of an integer in $\mathbb Z/m$. Thus the scalar $a$ acting on a vector of maximal additive order (a primitive vector) in $(\mathbb Z/m)^2$ is realised by the mod $m$ reduction of an integral unimodular matrix; no claim is made that $\gamma$ acts as $a$ on all of $(\mathbb Z/m)^2$, only on the given $w$.
--
--   This is the standard statement that the stabiliser of a primitive vector of $(\mathbb Z/m)^2$ inside $\mathrm{SL}_2(\mathbb Z/m)$ contains all unit scalar actions on that vector, used in the analysis of orbits of primitive vectors under congruence subgroups. It is cited in the computation bounding the number of orbits of $\Gamma_1$ on the relevant set of vectors by the index of $\Gamma_H$ together with $\pm 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
    (m : ℕ) [NeZero m] (w : ZMod m × ZMod m) (hw : addOrderOf w = m) (a : (ZMod m)ˣ) :
    ∃ γ : SL(2, ℤ),
      ((γ 0 0 : ℤ) : ZMod m) * w.1 + ((γ 0 1 : ℤ) : ZMod m) * w.2 = (a : ZMod m) * w.1 ∧
      ((γ 1 0 : ℤ) : ZMod m) * w.1 + ((γ 1 1 : ℤ) : ZMod m) * w.2 = (a : ZMod m) * w.2 := by sorry
