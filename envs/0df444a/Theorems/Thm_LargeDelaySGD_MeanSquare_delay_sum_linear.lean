-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_linear
-- name    : LargeDelaySGD.MeanSquare.delay_sum_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:52.372819+00:00
-- url     : https://prove2.me/theorems/f5577914-c22e-4b74-ab0b-1e54d893a284
-- title:
--   (B.9), App. B.1.1, p. 25 — linear delays, α_n ∝ 1/(n log n): Σα²_{n+1} < ∞, Σα_{n+1} = ∞, Σ_n α_{n+1} Σ_{r=s(n)}^{n−1} α_{r+1} < ∞
-- statement:
--   Let $(\alpha_n)_{n\ge0}$ be positive step sizes and $s:\mathbb N\to\mathbb N$ a delay schedule with $s(n)\le n$, satisfying the linear regime: $n-s(n)\le K(s(n)+1)$ for some $K$, and $\alpha_n=c/(n\log n)$ for all $n\ge N$, some $c>0$. Then
--
--   $$\sum_{n=0}^\infty\alpha_{n+1}^2<\infty,\qquad\sum_{n=0}^\infty\alpha_{n+1}=\infty,\qquad\sum_{n=0}^\infty\Big(\alpha_{n+1}\sum_{r=s(n)}^{n-1}\alpha_{r+1}\Big)<\infty.$$
--
--   These sums are the two error terms that remain after telescoping the descent inequality (B.5); their finiteness is what makes the delays harmless. The divergence $\sum\alpha_{n+1}=\infty$ is the paper's standing claim for each regime (Remark 2, p. 10; pp. 29–30), needed to pass from Lemmas 1–2 to Theorem 1.
--
--   **Formalization Note.** For nonnegative real series, "$<\infty$" is `Summable` and "$=\infty$" is `¬ Summable`. The regime's constants ($D$, $p$, $q$, $K$, $c$, $N$) are existential, as on the page; "$\propto$" holds from an index $N$ on.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, App. B.1.1, p. 25, case (3), (B.9); p. 24 ("in all cases in Assumption 2, we have Σ α²_{n+1} < ∞") and p. 26 ("in each of the above 4 cases")

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem delay_sum_linear (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (hreg : LinearRegime α s) :
    Summable (fun n => α (n + 1) ^ 2) ∧ ¬ Summable (fun n => α (n + 1)) ∧
      Summable (delaySum α s) := by sorry

end LargeDelaySGD.MeanSquare
