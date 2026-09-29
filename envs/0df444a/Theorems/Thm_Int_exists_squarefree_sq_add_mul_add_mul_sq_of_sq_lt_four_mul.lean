-- Prove2me | Theorems.Thm_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul
-- name    : Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/922e7ee1-f2b2-5600-8071-07c6c6138d01
-- title:
--   Positive-definite binary form represents a squarefree integer ≥ 2
-- statement:
--   Let $t$ and $n$ be integers satisfying $t^2 < 4n$, so that the binary quadratic form $Q(a,b) = a^2 + t\,ab + n\,b^2$ has negative discriminant $t^2 - 4n$ and is positive definite. The assertion is that there exist integers $a$ and $b$ with $b \neq 0$ such that the natural number $(a^2 + t\,ab + n\,b^2)\,$`.toNat`, that is the truncation to $\mathbb{N}$ of the integer value $Q(a,b)$, is squarefree as a natural number and is at least $2$. Since the value produced is in fact positive, the passage through `Int.toNat` loses nothing: the conclusion says that $Q$ takes, at some point off the line $b = 0$, a squarefree value $\ge 2$. Squarefreeness is the Mathlib predicate on the monoid $\mathbb{N}$: every element whose square divides the value is a unit.
--
--   For an imaginary quadratic order $\mathbb{Z}[\varphi]$ with $\varphi^2 = t\varphi - n$, the form $Q$ is the norm form, and $Q(a,b)$ is the degree of $a + b\varphi$ viewed as an endomorphism of an elliptic curve with complex multiplication by that order. The statement is used in the treatment of [`WeierstrassCurve.Affine.IsogenyEndDatum`](def/Isogeny_ConditionalCurrency.html#L149) to produce an endomorphism of squarefree degree $N \ge 2$ that is not multiplication by an integer, in the lemmas `exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j` and `exists_forall_pointEnd_eq_zsmul_of_transcendental_j`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat := by sorry
