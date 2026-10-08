-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_ineq15_distance_bound
-- name    : NonsmoothLojasiewicz.Convex.ineq15_distance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:35.754879+00:00
-- url     : https://prove2.me/theorems/8f0d60b5-276c-4336-b19b-df436cdf611d
-- title:
--   Inequality (15): $d_S(x)\le c^{-1/r}|f(x)-\min f|^{1/r}$ on bounded sets
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous, convex and subanalytic with $S:=\operatorname{crit} f\neq\emptyset$, and let $K\subseteq\mathbb R^n$ be bounded. Then there exist $r>1$ and $c>0$ such that
--   $$d_S(x)\le c^{-1/r}\,|f(x)-\min f|^{1/r}\qquad\text{for all }x\in K.$$
--
--   This is the growth condition of $f$ away from its solution set that subanalyticity provides, derived in the proof of Theorem 3.3 from the factorization lemma applied to the Moreau envelope.
--
--   **Formalization Note** The inequality is required at the points of $K$ where $f(x)<+\infty$; at the other points the right-hand side is $+\infty$ on the page and there is nothing to prove, while Lean's `toReal` would send $+\infty$ to $0$. $\min f$ is $\inf_y f(y)$, finite because $S\neq\emptyset$. The powers are real powers (`Real.rpow`) with real $r$.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1216, proof of Theorem 3.3, inequality (15)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Inequality (15) of Bolte–Daniilidis–Lewis (proof of Theorem 3.3, p. 1216): let
`f : ℝⁿ → ℝ ∪ {+∞}` be lower semicontinuous, convex and subanalytic with `S := crit f ≠ ∅`.
For every bounded set `K` there are `r > 1` and `c > 0` such that
`d_S(x) ≤ c^{−1/r} |f(x) − min f|^{1/r}` for all `x ∈ K ∩ dom f` (outside `dom f` the
right-hand side is `+∞` on the page). -/
theorem ineq15_distance_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f) (hcrit : (crit f).Nonempty)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K) :
    ∃ r : ℝ, 1 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, f x ≠ ⊤ →
      Metric.infDist x (crit f) ≤
        c ^ (-1 / r) * |(f x).toReal - (⨅ y, f y).toReal| ^ (1 / r) := by sorry

end NonsmoothLojasiewicz.Convex
