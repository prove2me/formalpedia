-- Prove2me | Theorems.Thm_FracRiccati_Radius_Supplement_theorem_3_3_b_resp_counterexample
-- name    : FracRiccati.Radius.Supplement.theorem_3_3_b_resp_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:54:52.916844+00:00
-- url     : https://prove2.me/theorems/a53e5217-60f6-495b-b70a-4777767fea3f
-- title:
--   Theorem 3.3(b), negative Moreover clause (corrected: counterexample to blow-up and noncontinuation)
-- statement:
--   The negative-sign clause is false. Set $\alpha=1$, $\lambda=\nu=-1$ and $\mu=-2$. The published recursion gives, for every $k\ge1$,
--   $$a_k=(-1)^k,\qquad R=1,\qquad \psi(t)=-\frac{t}{1+t}\quad(0\le t<1).$$
--   The function is strictly decreasing on $[0,1)$, but
--   $$\lim_{t\uparrow1}\psi(t)=-\frac12.$$
--   It has a continuous extension to $[0,2)$. Thus the decreasing assertion survives this example while the negative-infinite limit and claimed endpoint obstruction do not. This is a counterexample target, not an assertion of the printed false clause.
--
--   Differences from the source:
--   - correction: negative parameters force blow-up to negative infinity and prevent continuation → the explicit negative-parameter example has finite endpoint limit and a continuous extension; reason: at alpha=1 the recursion gives a_k=(-1)^k and the geometric series is -t/(1+t); see DISPROOF.md, item 1
--   - encoding: the limit is written at the radius → the limit is taken from [0,1) toward 1; reason: the exact radius is 1 in this example and only the convergent side defines the series
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 9, Theorem 3.3(b), Moreover clause (resp. λ, ν < 0, µ ≤ 0)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_Psi

namespace FracRiccati.Radius.Supplement

open Filter Topology

/-- Counterexample to the negative-sign blow-up and noncontinuation clauses. -/
theorem theorem_3_3_b_resp_counterexample :
    (∀ k : ℕ, 1 ≤ k → coeff 1 (-1) (-2) (-1) k = (-1 : ℂ) ^ k) ∧
    radius 1 (coeff 1 (-1) (-2) (-1)) = 1 ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, psiReal 1 (-1) (-2) (-1) t = -t / (1 + t)) ∧
    StrictAntiOn (psiReal 1 (-1) (-2) (-1)) (Set.Ico 0 1) ∧
    Tendsto (psiReal 1 (-1) (-2) (-1)) (nhdsWithin 1 (Set.Ico 0 1)) (nhds (-1 / 2)) ∧
    (∃ f : ℝ → ℝ, ContinuousOn f (Set.Ico 0 2) ∧
      Set.EqOn f (psiReal 1 (-1) (-2) (-1)) (Set.Ico 0 1)) := by sorry

end FracRiccati.Radius.Supplement
