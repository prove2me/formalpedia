-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal
-- name    : NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b3aa5f95-e524-57ff-b741-880df3fd524d
-- title:
--   Sign of the norm as product of signs at real places
-- statement:
--   Let $K$ be a number field (a field equipped with a `NumberField` structure, so in particular a finite extension of $\mathbb{Q}$) and let $x \in K$ be non-zero. The assertion is an equality in `SignType`: the sign of the rational number $\mathrm{N}_{K/\mathbb{Q}}(x)$, the value at $x$ of Mathlib's algebra norm `Algebra.norm ℚ`, equals the product over all $w$ in the subtype of infinite places of $K$ satisfying `InfinitePlace.IsReal w` of the sign of $\mathrm{embedding\_of\_isReal}(w)(x)$, the real number obtained by applying to $x$ the real embedding $K \to \mathbb{R}$ attached to the real place $w$ (the product is taken over the finite index type of real places, and is the empty product, namely $1$, when $K$ is totally complex). Both sides are elements of the three-element type of signs, so the statement records simultaneously that $\mathrm{N}_{K/\mathbb{Q}}(x)$ is non-zero and that its sign is the product of the signs of the real conjugates of $x$.
--
--   This is the standard comparison of the sign of a field norm with the signs of the real conjugates; in particular a totally positive element has positive norm, and in a totally complex field every non-zero element has positive norm. It is used in the project's estimates for sums of inverse powers of absolute norms over cyclotomic extensions, in [`NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension`](thm.html#NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension) and [`NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension`](thm.html#NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by sorry
