-- Prove2me | Theorems.Thm_LefebvreVariations_chebyshev_extremal_degree_two
-- name    : LefebvreVariations.chebyshev_extremal_degree_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:26:10.767813+00:00
-- url     : https://prove2.me/theorems/cab80464-c2e7-5eb9-abd1-c228fbb6e966
-- title:
--   Lefebvre's variations, No. 271 — on a theme by Frongillo, Monroe, Neyman and Waggoner: the best degree two polynomial normalised at zero on the interval from 1 to n has sup norm (n-1)^2 over n^2+6n+1
-- statement:
--   For every integer $n\ge2$,
--   $$
--   \min\Bigl\{\ \max_{x\in[1,n]}|p(x)|\ :\ p\in\mathbb{R}[x],\ \deg p\le2,\ p(0)=1\Bigr\}\;=\;\frac{(n-1)^2}{n^2+6n+1}.
--   $$
--   The minimum is attained by
--   $$
--   \hat T_2(x)\;=\;\frac{T_2(m(x))}{T_2(m(0))},\qquad m(x)=\frac{2x-(n+1)}{n-1},\quad T_2(t)=2t^2-1,
--   $$
--   and $\hat T_2$ is the only polynomial of degree at most $2$ with $p(0)=1$ that attains it.
--
--   This is the case $d=2$ of the formula $2/\bigl(q(n)^d+q(n)^{-d}\bigr)$, $q(n)=(\sqrt n+1)/(\sqrt n-1)$, for the best sup-norm on $[1,n]$ of a degree-$d$ polynomial normalised at $0$; for $d=2$ one has $q^2+q^{-2}=(2n^2+12n+2)/(n-1)^2$. It is Chebyshev's minimax property of $T_2$ moved to $[1,n]$: $|m(0)|=(n+1)/(n-1)$ and $T_2(m(0))=(n^2+6n+1)/(n-1)^2$.
--
--   **Formalization Note** The statement uses the platform definitions `ivlSet`, `IsIvlMinimizer` and `chebHat` of the `RobustFcstAgg` namespace, at `d = 2`; `ivlSet n 2` is the set of bounds `E` such that some `p` of degree at most `2` with `p(0) = 1` has `|p(x)| ≤ E` on `[1, n]`, so `IsLeast` states that the minimum exists and equals the closed form. The closed form is written with real casts of `n`, not through `qn`. This is `RobustFcstAgg.lemma_10` at `d = 2`.
--
--   **Why this is a variation.** This varies the open platform problem RobustFcstAgg.lemma_10 (the minimum over polynomials of degree at most d with p(0) = 1 of the sup norm on [1,n] is 2/(q(n)^d + q(n)^-d), attained only by the transformed Chebyshev polynomial). It is the case d = 2, the first degree with a nonlinear extremal polynomial, in the parent's own definitions and with the closed form (n-1)^2/(n^2+6n+1) made explicit.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. Frongillo, I. Monroe, E. Neyman and B. Waggoner, Robust forecast aggregation via additional queries, arXiv:2512.05271, Lemma 10 (as quoted on the platform); P. L. Chebyshev's minimax property of the polynomials T_d (cited from memory, no reference given). The closed form and the uniqueness were checked numerically for n = 2, 3, 5, 10 (grid of 4001 points and a random local search over the two free coefficients): the search minimum agrees with (n-1)^2/(n^2+6n+1) to 4 digits and never goes below it, and the sup norm of T_2(m(x))/T_2(m(0)) equals it.

import Mathlib
import Definitions.Def_RobustFcstAgg_ivlSet
import Definitions.Def_RobustFcstAgg_IsIvlMinimizer
import Definitions.Def_RobustFcstAgg_chebHat

set_option autoImplicit false

open Polynomial RobustFcstAgg

namespace LefebvreVariations

/-- **The Chebyshev extremal problem of degree two on `[1, n]`.** For every integer `n ≥ 2`,
`min { max_{x ∈ [1,n]} |p(x)| : deg p ≤ 2, p(0) = 1 } = (n − 1)² / (n² + 6n + 1)`, the minimum is attained by the
transformed Chebyshev polynomial `T̂₂(x) = T₂(m(x))/T₂(m(0))` with `m(x) = (2x − n − 1)/(n − 1)`, and by no other
polynomial. This is the case `d = 2` of the formula `2/(q(n)^d + q(n)^{-d})`, `q(n) = (√n + 1)/(√n − 1)`, of
Frongillo, Monroe, Neyman and Waggoner, *Robust forecast aggregation via additional queries*, arXiv:2512.05271,
Lemma 10 (cited as on the platform); with `a = √n + 1`, `b = √n − 1` one has `q² + q⁻² = (a⁴ + b⁴)/(ab)² =
(2n² + 12n + 2)/(n − 1)²`. The underlying fact is Chebyshev's minimax property of `T_d` (Chebyshev, 1854; Markov).

**Formalization Note.** Same `ivlSet`, `IsIvlMinimizer` and `chebHat` as `RobustFcstAgg.lemma_10`, at `d = 2`, with the
closed form written in `n` (real casts) instead of `qn`. -/
theorem chebyshev_extremal_degree_two (n : ℕ) (hn : 2 ≤ n) :
    IsLeast (ivlSet n 2) (((n : ℝ) - 1) ^ 2 / ((n : ℝ) ^ 2 + 6 * n + 1)) ∧
    IsIvlMinimizer n 2 (chebHat n 2) ∧
    ∀ p : ℝ[X], IsIvlMinimizer n 2 p → p = chebHat n 2 := by
  sorry

end LefebvreVariations
