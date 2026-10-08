-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_eq27_er1_one_sided_derivs
-- name    : NestedSeatAlloc.ProbCond.eq27_er1_one_sided_derivs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:07.464001+00:00
-- url     : https://prove2.me/theorems/f090e2d2-543a-4042-ade8-dd2f1c6544ae
-- title:
--   (27), p. 132 — ER₁ is concave with δER₁[s; p; X] = [f₁Pr[X₁ > s], f₁Pr[X₁ ≥ s]]
-- statement:
--   Let $X_1 \ge 0$ be a nonnegative random variable (the class-1 demand) on a probability space $(\Omega, \mathcal F, P)$, let $f_1 \ge 0$ be the class-1 fare, and let $ER_1[s; p; X] = E\,R_1[s; p; X] = f_1\,E[\min(s, X_1)]$ be the expected revenue of the highest fare class with $s$ seats available (it does not depend on the policy $p$). Then:
--   1. $ER_1[\,\cdot\,; p; X]$ is concave on $s \ge 0$;
--   2. for every $s \ge 0$ its right derivative is
--   $$\delta_+ ER_1[s; p; X] = f_1 \Pr[X_1 > s];$$
--   3. for every $s > 0$ its left derivative is
--   $$\delta_- ER_1[s; p; X] = f_1 \Pr[X_1 \ge s].$$
--
--   Together, (2) and (3) are equation (27): $\delta ER_1[s; p; X] = [f_1 \Pr[X_1 > s], f_1 \Pr[X_1 \ge s]]$. This is the base case of both inductions of the paper: the concavity induction of Theorem 1 and the derivative formula of Lemma 2.
--
--   **Formalization Note** The page states (27) inside the proof of Theorem 2, where demand is integer valued, but its derivation from (21)–(22) does not use integrality, and it is stated here for real-valued demand. The concavity conjunct is the base case "$E\{R_1[s; p; X] \mid X_1\}$ is concave in $s$ for any policy $p$" of the proof of Theorem 1, p. 132. The hypotheses kept are: $P$ is a probability measure, and $X_1$ is measurable and nonnegative (§1: demands are nonnegative; without it a non-integrable negative tail turns the Bochner integral into the junk value $0$). The fare $f_1$ is assumed nonnegative: the page calls $[f_1\Pr[X_1 > s], f_1\Pr[X_1 \ge s]]$ a subdifferential and $ER_1$ concave, which both require $f_1 \ge 0$ (fares are revenues, p. 129); with $f_1 < 0$ the function $f_1 E[\min(s, X_1)]$ is convex. Independence and the fare ordering are dropped, which makes the statement stronger. At $s = 0$ the left derivative is the convention $+\infty$ and is not stated.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), (27), p. 132, with (21)–(22), p. 132; concavity of E{R_1|X_1}, proof of Theorem 1, p. 132

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- (27), p. 132, with (21)–(22), and the base case of the proof of Theorem 1: for a nonnegative demand `X₁`
(§1) and a nonnegative fare `f₁`, `ER_1[s; p; X]` is concave on `s ≥ 0`, its right derivative at `s ≥ 0` is
`f₁ Pr[X₁ > s]`, and its left derivative at `s > 0` is `f₁ Pr[X₁ ≥ s]`. -/
theorem eq27_er1_one_sided_derivs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hX : Measurable (X 1))
    (hX0 : ∀ ω, 0 ≤ X 1 ω) (hf1 : 0 ≤ f 1) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1) ∧
      (∀ s, 0 ≤ s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s) ∧
      (∀ s, 0 < s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s ≤ X 1 ω}) (Set.Iic s) s) := by sorry

end NestedSeatAlloc.ProbCond
