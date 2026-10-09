-- Prove2me | Theorems.Thm_ModernOnlineLearning_Aggregating_proposition_7_34
-- name    : ModernOnlineLearning.Aggregating.proposition_7_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:06.500445+00:00
-- url     : https://prove2.me/theorems/c100d3f4-c261-471f-914c-bdb9a467dc02
-- title:
--   Proposition 7.34, p. 124 — exp-concavity implies convexity
-- statement:
--   Let $V\subseteq\mathbb R^d$ be convex, $\alpha>0$, and let $f:\mathbb R^d\to(-\infty,+\infty]$. If $x\mapsto e^{-\alpha f(x)}$ is concave on $V$, with $e^{-\alpha(+\infty)}=0$, then $f$ is convex on $V$:
--
--   $$\operatorname{epi}_V(f)=\{(x,r)\in V\times\mathbb R:f(x)\leq r\}\quad\text{is convex.}$$
--
--   This locates the exp-concave loss class within ordinary convex losses.
--
--   **Formalization Note** Convexity of the epigraph is equivalent to the usual extended-real convexity inequality. `WithTop ℝ` models finite real values and $+\infty$, with no $-\infty$, exactly as in the source.
-- source:
--   Orabona, arXiv:1912.13213v10, Proposition 7.34, p. 124

import Mathlib
import Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
set_option autoImplicit false

namespace ModernOnlineLearning.Aggregating

/-- Proposition 7.34, p. 124, for the source's `(−∞, +∞]` losses. -/
theorem proposition_7_34 {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}
    {α : ℝ} {f : EuclideanSpace ℝ (Fin d) → WithTop ℝ}
    (hα : 0 < α) (hf : ExpConcaveOnExtended V α f) : ExtendedConvexOn V f := by sorry

end ModernOnlineLearning.Aggregating
