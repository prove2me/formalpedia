-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_remark35_growth_lojasiewicz
-- name    : NonsmoothLojasiewicz.Convex.remark35_growth_lojasiewicz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:46.764097+00:00
-- url     : https://prove2.me/theorems/913fe4a1-249b-4011-bc2e-d0f82ca7cc73
-- title:
--   Remark 3.5: the growth condition (17) alone gives a Łojasiewicz inequality
-- statement:
--   Let $K\subseteq\mathbb R^n$ be compact and let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous and convex (not necessarily subanalytic) with $S:=\operatorname{crit} f\neq\emptyset$. Assume the growth condition
--   $$|f(x)-\min f|\ge c\,d_S(x)^r\qquad\text{for all }x\in K,\tag{17}$$
--   with $c>0$ and $r\ge 1$. Then $f$ satisfies a Łojasiewicz inequality around every critical point $a$ in the interior of $K$: there is an exponent $\theta\in[0,1)$ such that $|f-f(a)|^{\theta}/m_f$ is bounded on a neighbourhood of $a$.
--
--   The remark isolates what the proof of Theorem 3.3 actually uses: not subanalyticity itself but the growth condition it implies.
--
--   **Formalization Note** (17) is imposed at the points of $K$ with $f(x)<+\infty$ (elsewhere its left-hand side is $+\infty$). The conclusion uses the `LojIneqAt` definition (inequality (8)), in which $f(a)=\min f$. $\theta$ is existential, as on the page.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1216, Remark 3.5, condition (17)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
import Definitions.Def_NonsmoothLojasiewicz_Continuous_LojIneqAt

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Remark 3.5 of Bolte–Daniilidis–Lewis (p. 1216): let `K` be compact and `f : ℝⁿ → ℝ ∪ {+∞}`
lower semicontinuous and convex (not necessarily subanalytic), with `S := crit f ≠ ∅`,
satisfying the growth condition (17): `|f(x) − min f| ≥ c d_S(x)^r` for all `x ∈ K`, where
`c > 0` and `r ≥ 1`. Then `f` satisfies a Łojasiewicz inequality around every critical point `a`
in the interior of `K`: there is `θ ∈ [0, 1)` such that `|f − f(a)|^θ / m_f` is bounded around
`a`. Condition (17) is imposed at the points of `K ∩ dom f` (elsewhere its left side is `+∞`). -/
theorem remark35_growth_lojasiewicz {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hcrit : (crit f).Nonempty)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (c r : ℝ) (hc : 0 < c) (hr : 1 ≤ r)
    (h17 : ∀ x ∈ K, f x ≠ ⊤ →
      c * Metric.infDist x (crit f) ^ r ≤ |(f x).toReal - (⨅ y, f y).toReal|)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) (haK : a ∈ interior K) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ NonsmoothLojasiewicz.Continuous.LojIneqAt f a θ := by sorry

end NonsmoothLojasiewicz.Convex
