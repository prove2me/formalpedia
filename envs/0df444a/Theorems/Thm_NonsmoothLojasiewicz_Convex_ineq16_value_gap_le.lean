-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_ineq16_value_gap_le
-- name    : NonsmoothLojasiewicz.Convex.ineq16_value_gap_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:08.561219+00:00
-- url     : https://prove2.me/theorems/cbfa1125-341d-403f-9e1c-fc15b139f5ed
-- title:
--   Inequality (16): $|f(x)-\min f|\le\|x^*\|\,d_S(x)$ for lsc convex $f$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous and convex with $S:=\operatorname{crit} f\neq\emptyset$, and write $d_S(x)=\inf\{\|x-a\|:a\in S\}$. Then for every $x\in\mathbb R^n$ and every limiting subgradient $x^*\in\partial f(x)$,
--   $$|f(x)-\min f|\le\|x^*\|\,d_S(x).$$
--
--   The inequality converts a lower bound on the distance to the solution set into an upper bound on the function gap, and is the step that turns the growth condition (15) into the Łojasiewicz inequality. The paper notes (Remark 3.6) that it holds for every lower semicontinuous convex function.
--
--   **Formalization Note** $\min f$ is written $\inf_y f(y)$ (an `EReal`); with $\operatorname{crit} f\neq\emptyset$ it is finite and attained. A subgradient at $x$ forces $f(x)$ finite, so `toReal` returns the true values.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1216, proof of Theorem 3.3, inequality (16)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Inequality (16) of Bolte–Daniilidis–Lewis (p. 1216): for a lower semicontinuous convex
`f : ℝⁿ → ℝ ∪ {+∞}` with `S := crit f ≠ ∅`, every `x` and every limiting subgradient
`x* ∈ ∂f(x)` satisfy `|f(x) − min f| ≤ ‖x*‖ d_S(x)`. Here `min f` is `⨅ y, f y` (finite and
attained on `crit f`), and `f x` is finite because `∂f(x) ≠ ∅`. -/
theorem ineq16_value_gap_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hcrit : (crit f).Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ LimitingSubdiff f x) :
    |(f x).toReal - (⨅ y, f y).toReal| ≤ ‖v‖ * Metric.infDist x (crit f) := by sorry

end NonsmoothLojasiewicz.Convex
