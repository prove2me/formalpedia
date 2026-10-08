-- Prove2me | Theorems.Thm_MatrixTail_Bernstein_bennettH_ge
-- name    : MatrixTail.Bernstein.bennettH_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:55.477978+00:00
-- url     : https://prove2.me/theorems/2ba015af-0913-47d9-bd76-0978380c50ae
-- title:
--   Proof of Theorem 6.1 — numerical bound h(u) ≥ (u²/2)/(1 + u/3) for u ≥ 0
-- statement:
--   Let $h(u)=(1+u)\log(1+u)-u$ be Bennett's function. For every $u\ge0$,
--   $$h(u)\ge\frac{u^2/2}{1+u/3}.$$
--
--   This elementary inequality is the step by which the Bennett bound (i) of Theorem 6.1 implies the Bernstein bound (ii): substituting $u=Rt/\sigma^2$ turns $\frac{\sigma^2}{R^2}\cdot\frac{u^2/2}{1+u/3}$ into $\frac{t^2/2}{\sigma^2+Rt/3}$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 26, proof of Theorem 6.1 (unnumbered numerical bound)

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- The numerical bound in the **proof of Theorem 6.1**, Tropp, arXiv:1004.4389v7, p. 26 (unnumbered):
`h(u) ≥ (u²/2)/(1 + u/3)` for `u ≥ 0`, where `h(u) = (1 + u) log(1 + u) − u` is Bennett's function.
It is what makes the Bennett inequality (i) imply the Bernstein inequality (ii).

Formalization Note: at `u ≥ 0` the denominator `1 + u/3` is positive and `log(1 + u)` is the genuine logarithm,
so no junk value arises. -/
theorem bennettH_ge (u : ℝ) (hu : 0 ≤ u) :
    (u ^ 2 / 2) / (1 + u / 3) ≤ bennettH u := by sorry

end MatrixTail.Bernstein
