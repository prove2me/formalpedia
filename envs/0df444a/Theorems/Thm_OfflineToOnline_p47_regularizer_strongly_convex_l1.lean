-- Prove2me | Theorems.Thm_OfflineToOnline_p47_regularizer_strongly_convex_l1
-- name    : OfflineToOnline.p47_regularizer_strongly_convex_l1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:29.332018+00:00
-- url     : https://prove2.me/theorems/00ffab35-df9f-4674-b50b-bec9c0075906
-- title:
--   p.47 display (corrected: $1/(9\log d)$, $d\ge8$) — $\frac12\|x\|_q^2$ is strongly convex w.r.t. $\ell_1$
-- statement:
--   Let $d\ge8$ and $q=\dfrac{\log d}{\log d-1}$ (natural logarithm). The regularizer
--
--   $$
--   R(x)=\tfrac12\|x\|_q^2,\qquad \|x\|_q=\Big(\sum_{j=1}^d|x_j|^q\Big)^{1/q},
--   $$
--
--   is $\dfrac{1}{9\log d}$-strongly convex on $\mathbb R^d$ with respect to the $\ell_1$ norm.
--
--   Because its modulus degrades only logarithmically in $d$, FTRL with this regularizer has regret proportional to $\sqrt{\log d}$ against losses bounded in $\ell_\infty$; this is where the $\sqrt{\log d}$ of Theorems 1 and 2 comes from.
--
--   Differences from the source:
--   - correction: R is 1/(3 log(d))-strongly convex with respect to the ℓ1 norm, for every d → R is 1/(9 log d)-strongly convex with respect to ℓ1, for d ≥ 8; reason: squaring ‖w‖₁/3 ≤ ‖w‖_q gives ‖w‖₁²/9, not /3; for d = 8, x = 𝟙, h = (1,−1,…,1,−1) the second derivative of R along h over ‖h‖₁² is (q−1)/e² ≈ 0.1254 < 1/(3 ln 8) ≈ 0.1603; q ∈ (1,2), Lemma 3's range, holds exactly when d ≥ 8, and for d ≤ 7 the printed q is ≤ 0, undefined, or > 2
--   - encoding: μ-strongly convex function (footnote 23: differentiable, first-order inequality) → Mathlib's StrongConvexOn on all of ℝ^d with the ℓ1 norm of PiLp 1; reason: the two agree for differentiable functions; R is differentiable away from 0 and convex
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, display and text, p.47

import Mathlib

namespace OfflineToOnline

/-- **p.47 display** (corrected: modulus `1/(9 log d)`, `d ≥ 8`). For every `d ≥ 8`, with
`q = log d / (log d − 1)`, the regularizer `R(x) = ½‖x‖_q²` is `1/(9 log d)`-strongly convex on
`ℝ^d` with respect to the `ℓ1` norm.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, p.47 ("So, the function R is 1/(3 log(d))-strongly convex with respect to the ℓ1 norm").

Formalization Note: the page claims modulus `1/(3 log d)`, squaring `‖w‖₁/3 ≤ ‖w‖_q` as
`‖w‖₁²/3`. That is false: for `d = 8`, `x = 𝟙`, `h = (1, −1, …, 1, −1)`, the second derivative of `R`
along `h` divided by `‖h‖₁²` is `(q − 1)/e² ≈ 0.1254 < 1/(3 ln 8) ≈ 0.1603`. Squaring correctly gives
`1/(9 log d)`. The restriction `d ≥ 8` is exactly where `q ∈ (1, 2)` (Lemma 3's range); for `d ≤ 7`
the printed `q` is `≤ 0`, undefined, or `> 2`. `log` is the natural logarithm. `ℝ^d` with the `ℓ1`
norm is `PiLp 1`; `‖x‖_q` is written out as `(∑_j |x_j|^q)^{1/q}`. -/
theorem p47_regularizer_strongly_convex_l1 (d : ℕ) (hd : 8 ≤ d) :
    StrongConvexOn Set.univ (1 / (9 * Real.log d))
      (fun x : PiLp 1 (fun _ : Fin d => ℝ) =>
        (1 / 2 : ℝ) * ((∑ j, |x j| ^ (Real.log d / (Real.log d - 1))) ^
          (1 / (Real.log d / (Real.log d - 1)))) ^ 2) := by sorry

end OfflineToOnline
