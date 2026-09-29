-- Prove2me | Theorems.Thm_IsNonarchimedean_iSup_abv_mul_sub_mul_eq_iSup_abv_sub
-- name    : IsNonarchimedean.iSup_abv_mul_sub_mul_eq_iSup_abv_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/cb3ff8cf-56e0-5ab4-9ca1-17054a4f97c6
-- title:
--   Ultrametric 2× 2 minors at a common pivot
-- statement:
--   Let $K$ be a field and $\mu \colon K \to \mathbb{R}$ an absolute value which is non-archimedean, i.e. $\mu(a+b) \le \max(\mu(a),\mu(b))$ for all $a,b \in K$. Let $r$ be a natural number and let $x, v \colon \mathrm{Fin}\,r \to K$ be two families of elements of $K$ indexed by $\{0,\dots,r-1\}$. Suppose there is an index $i$ with $x_i = 1$ and $v_i = 1$, and suppose $\mu(x_l) \le 1$ and $\mu(v_l) \le 1$ for every index $l$. Then the two suprema of real numbers
--   $$\sup_{(l,m)} \mu(x_l v_m - x_m v_l) \qquad\text{and}\qquad \sup_{l} \mu(x_l - v_l),$$
--   the first taken over all pairs of indices and the second over all indices, are equal. Both suprema are taken in $\mathbb{R}$ over finite, nonempty index types (nonempty because of $i$), so they are attained maxima.
--
--   In the non-archimedean geometry of projective space this is the statement that, for two points of $\mathbb{P}^{r-1}(K)$ given by integral coordinate vectors normalised at the same pivot coordinate $i$, the numerator of the chordal distance — the supremum of the $2\times 2$ minors — coincides with the $\ell^\infty$-distance of the two vectors in the affine chart determined by $i$. It is used in the construction of charts at a pivot for the modular curve, via [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsNonarchimedean_iSup_abv_mul_sub_mul_eq_iSup_abv_sub.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem IsNonarchimedean.iSup_abv_mul_sub_mul_eq_iSup_abv_sub
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (i : Fin r) (hxi : x i = 1) (hvi : v i = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) = ⨆ l, μ (x l - v l) := by sorry
