-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_remark36_bounded_ratio
-- name    : NonsmoothLojasiewicz.Convex.remark36_bounded_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:16.94298+00:00
-- url     : https://prove2.me/theorems/0909e1e9-ab1a-49df-9b68-ea7bb054e6da
-- title:
--   Remark 3.6: $|f-\min f|/m_f$ is bounded around critical points of lsc convex $f$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous and convex (not necessarily subanalytic), and let $a\in\operatorname{crit} f$. Then the function
--   $$\frac{|f-\min f|}{m_f}$$
--   is bounded around $a$: there are a constant $C$ and a neighbourhood $U$ of $a$ such that $|f(x)-\min f|\le C\,\|x^*\|$ for all $x\in U$ and all $x^*\in\partial f(x)$.
--
--   This is the weak form (exponent $\theta=1$, outside $[0,1)$) of the Łojasiewicz inequality (14), valid for every lower semicontinuous convex function; Theorem 3.3 improves the exponent under subanalyticity.
--
--   **Formalization Note** The bounded ratio is encoded without division, with the conventions $\infty/\infty=0/0=0$: points with $\partial f(x)=\emptyset$ impose nothing. $\min f$ is $\inf_y f(y)$, finite because $a$ is a minimizer.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1216, Remark 3.6

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Remark 3.6 of Bolte–Daniilidis–Lewis (p. 1216): for a lower semicontinuous convex
`f : ℝⁿ → ℝ ∪ {+∞}` (not necessarily subanalytic), the ratio `|f − min f| / m_f` is bounded
around every critical point `a` of `f`: there are `C` and a neighbourhood `U` of `a` with
`|f(x) − min f| ≤ C ‖x*‖` for all `x ∈ U` and all `x* ∈ ∂f(x)`. -/
theorem remark36_bounded_ratio {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) :
    ∃ C : ℝ, ∃ U ∈ 𝓝 a, ∀ x ∈ U, ∀ v ∈ LimitingSubdiff f x,
      |(f x).toReal - (⨅ y, f y).toReal| ≤ C * ‖v‖ := by sorry

end NonsmoothLojasiewicz.Convex
