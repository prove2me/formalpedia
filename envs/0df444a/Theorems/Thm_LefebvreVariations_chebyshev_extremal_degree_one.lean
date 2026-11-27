-- Prove2me | Theorems.Thm_LefebvreVariations_chebyshev_extremal_degree_one
-- name    : LefebvreVariations.chebyshev_extremal_degree_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:25:36.009593+00:00
-- url     : https://prove2.me/theorems/a6126603-4b75-4bbe-8708-4842a51dd5ca
-- title:
--   Lefebvre's variations, No. 270 — on a theme by Frongillo, Monroe, Neyman and Waggoner: the best linear polynomial normalised at zero on the interval from 1 to n has sup norm (n-1) over (n+1)
-- statement:
--   For every integer $n\ge2$,
--   $$
--   \min\Bigl\{\ \max_{x\in[1,n]}|p(x)|\ :\ p\in\mathbb{R}[x],\ \deg p\le1,\ p(0)=1\Bigr\}\;=\;\frac{n-1}{n+1}.
--   $$
--   The minimum is attained by
--   $$
--   \hat T_1(x)\;=\;\frac{T_1(m(x))}{T_1(m(0))}\;=\;1-\frac{2x}{n+1},\qquad m(x)=\frac{2x-(n+1)}{n-1},
--   $$
--   and $\hat T_1$ is the only polynomial of degree at most $1$ with $p(0)=1$ that attains it.
--
--   This is the case $d=1$ of the formula $2/\bigl(q(n)^d+q(n)^{-d}\bigr)$, $q(n)=(\sqrt n+1)/(\sqrt n-1)$, for the best sup-norm on $[1,n]$ of a degree-$d$ polynomial normalised at $0$: for $d=1$, $2/(q+q^{-1})=2(n-1)/(2n+2)$. Elementary argument: for $p(x)=1-cx$ the extreme values on $[1,n]$ are $|1-c|$ and $|1-cn|$, and they balance, $1-c=-(1-cn)$, exactly at $c=2/(n+1)$.
--
--   **Formalization Note** The statement uses the platform definitions `ivlSet`, `IsIvlMinimizer` and `chebHat` of the `RobustFcstAgg` namespace, at `d = 1`; `ivlSet n 1` is the set of bounds `E` such that some `p` of degree at most `1` with `p(0) = 1` has `|p(x)| ≤ E` on `[1, n]`, so `IsLeast` states that the minimum exists and equals the closed form. The closed form is written with real casts of `n`, not through `qn`. This is `RobustFcstAgg.lemma_10` at `d = 1`.
--
--   **Why this is a variation.** This varies the open platform problem RobustFcstAgg.lemma_10 (the minimum over polynomials of degree at most d with p(0) = 1 of the sup norm on [1,n] is 2/(q(n)^d + q(n)^-d), attained only by the transformed Chebyshev polynomial). It is the case d = 1, where the extremal polynomial is the line 1 - 2x/(n+1) and the value is (n-1)/(n+1), stated in the parent's own definitions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. Frongillo, I. Monroe, E. Neyman and B. Waggoner, Robust forecast aggregation via additional queries, arXiv:2512.05271, Lemma 10 (as quoted on the platform). The statement is elementary (equioscillation of the linear polynomial at the two end points) and was checked numerically for n = 2, 3, 5, 10 (grid search over the slope: minimum (n-1)/(n+1) to 4 digits).

import Mathlib
import Definitions.Def_RobustFcstAgg_ivlSet
import Definitions.Def_RobustFcstAgg_IsIvlMinimizer
import Definitions.Def_RobustFcstAgg_chebHat

set_option autoImplicit false

open Polynomial RobustFcstAgg

namespace LefebvreVariations

/-- **The Chebyshev extremal problem of degree one on `[1, n]`.** For every integer `n ≥ 2`,
`min { max_{x ∈ [1,n]} |a + bx| : a = 1 } = (n − 1)/(n + 1)`, attained exactly by `p(x) = 1 − 2x/(n + 1)`, which is the
transformed Chebyshev polynomial `T̂₁`. This is the case `d = 1` of the formula `2/(q(n)^d + q(n)^{-d})`,
`q(n) = (√n + 1)/(√n − 1)`, of Frongillo, Monroe, Neyman and Waggoner, *Robust forecast aggregation via additional
queries*, arXiv:2512.05271, Lemma 10 (cited as on the platform): `2/(q + q⁻¹) = 2(n − 1)/(2n + 2)`. Elementary
argument: the equioscillation `p(1) = −p(n)` forces the slope `−2/(n + 1)`.

**Formalization Note.** Same `ivlSet`, `IsIvlMinimizer` and `chebHat` as `RobustFcstAgg.lemma_10`, at `d = 1`, with the
closed form written in `n` (real casts) instead of `qn`. -/
theorem chebyshev_extremal_degree_one (n : ℕ) (hn : 2 ≤ n) :
    IsLeast (ivlSet n 1) (((n : ℝ) - 1) / ((n : ℝ) + 1)) ∧
    IsIvlMinimizer n 1 (chebHat n 1) ∧
    ∀ p : ℝ[X], IsIvlMinimizer n 1 p → p = chebHat n 1 := by
  sorry

end LefebvreVariations
