-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_bounded
-- name    : LargeDelaySGD.MeanSquare.delay_sum_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:51.609783+00:00
-- url     : https://prove2.me/theorems/99f2bf50-23d1-4d91-885b-7a76fb09cb19
-- title:
--   Delay sum, App. B.1.1, p. 25, case (1) — bounded delays: Σ α²_{n+1} < ∞ and Σ_n α_{n+1} Σ_{r=s(n)}^{n−1} α_{r+1} < ∞
-- statement:
--   Let $(\alpha_n)_{n\ge0}$ be positive step sizes and $s:\mathbb N\to\mathbb N$ a delay schedule with $s(n)\le n$, satisfying the bounded-delay regime: $n-s(n)\le D$ for some $D$, $\sum_n\alpha_n^2<\infty$ and $\sum_n\alpha_n=\infty$. Then
--
--   $$\sum_{n=0}^\infty\alpha_{n+1}^2<\infty\qquad\text{and}\qquad\sum_{n=0}^\infty\Big(\alpha_{n+1}\sum_{r=s(n)}^{n-1}\alpha_{r+1}\Big)<\infty.$$
--
--   These sums are the two error terms that remain after telescoping the descent inequality (B.5); their finiteness is what makes the delays harmless.
--
--   **Formalization Note.** For nonnegative real series, "$<\infty$" is `Summable` and "$=\infty$" is `¬ Summable`. The regime's constants ($D$, $p$, $q$, $K$, $c$, $N$) are existential, as on the page; "$\propto$" holds from an index $N$ on.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, App. B.1.1, p. 25, case (1); p. 24 ("in all cases in Assumption 2, we have Σ α²_{n+1} < ∞") and p. 26 ("in each of the above 4 cases")

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem delay_sum_bounded (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (hreg : BoundedRegime α s) :
    Summable (fun n => α (n + 1) ^ 2) ∧ Summable (delaySum α s) := by sorry

end LargeDelaySGD.MeanSquare
