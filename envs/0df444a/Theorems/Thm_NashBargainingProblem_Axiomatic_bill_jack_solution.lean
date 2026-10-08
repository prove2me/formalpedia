-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_bill_jack_solution
-- name    : NashBargainingProblem.Axiomatic.bill_jack_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:22.291214+00:00
-- url     : https://prove2.me/theorems/4be9b1ab-8aaf-42ed-8180-c4c0bec27246
-- title:
--   p. 161 — Bill and Jack: the Nash product is maximized at the vertex (12, 5), reached by one exchange
-- statement:
--   In Nash's Bill–Jack barter (goods, additive utilities, exchange gains and the set of alternatives $S_{BJ}$ as in the definition `BillJack`):
--
--   1. $(12,5)\in S_{BJ}$, and it is the strict maximizer of the product of the utility gains over $S_{BJ}$ in the closed first quadrant: every $s\in S_{BJ}$ with $s_1,s_2\ge0$ and $s\ne(12,5)$ has $s_1s_2<60$;
--   2. $(12,5)$ is an extreme point (a vertex) of the polygon $S_{BJ}$;
--   3. exactly one exchange has gain $(12,5)$: $\mathrm{gain}(X,Y)=(12,5)$ if and only if Bill gives Jack $X=\{\text{book, whip, ball, bat}\}$ and Jack gives Bill $Y=\{\text{pen, toy, knife}\}$.
--
--   This is the solution Nash reports for the example: Bill gains $20-8=12$ and Jack gains $9-4=5$.
--
--   **Formalization Note** "There is but one corresponding anticipation" is read for pure exchanges: a lottery over exchanges whose expected gain is a vertex of the hull is degenerate. "A convex polygon" is not stated separately, since the convex hull of finitely many points is one.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 161, Examples ("It turns out to be a convex polygon in which the point where the product of the utility gains is maximized is at a vertex and where there is but one corresponding anticipation."), Figure 2

import Mathlib
import Definitions.Def_NashBargainingProblem_Axiomatic_BillJack

namespace NashBargainingProblem.Axiomatic
theorem bill_jack_solution :
    ((12 : ℝ), (5 : ℝ)) ∈ billJackSet ∧
    (∀ s ∈ billJackSet, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ ((12 : ℝ), (5 : ℝ)) →
      s.1 * s.2 < 12 * 5) ∧
    ((12 : ℝ), (5 : ℝ)) ∈ billJackSet.extremePoints ℝ ∧
    ∀ (X : Finset BillGood) (Y : Finset JackGood),
      billJackGain (X, Y) = ((12 : ℝ), (5 : ℝ)) ↔
        X = {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat} ∧
        Y = {JackGood.pen, JackGood.toy, JackGood.knife} := by sorry
end NashBargainingProblem.Axiomatic
