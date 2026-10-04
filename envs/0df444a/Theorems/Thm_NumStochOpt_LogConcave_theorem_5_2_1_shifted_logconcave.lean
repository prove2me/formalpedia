-- Prove2me | Theorems.Thm_NumStochOpt_LogConcave_theorem_5_2_1_shifted_logconcave
-- name    : NumStochOpt.LogConcave.theorem_5_2_1_shifted_logconcave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:56:03.38332+00:00
-- url     : https://prove2.me/theorems/d7fdd6ea-88ae-4105-a29f-b58b9ad963d2
-- title:
--   Theorem 5.2.1 — if $h$ is log-concave on $H=\{h \ge p\}$ then $h - p$ is log-concave on $H$
-- statement:
--   Let $h : \mathbb R^n \to \mathbb R$ and let $p$ be a probability level with $0 < p < 1$. Suppose that the superlevel set
--
--   $$
--   H = \{x \in \mathbb R^n : h(x) \ge p\}
--   $$
--
--   is convex and that $h$ is logarithmically concave on $H$, i.e. $h(\lambda x + (1-\lambda)y) \ge h(x)^{\lambda} h(y)^{1-\lambda}$ for all $x, y \in H$ and $0 < \lambda < 1$. Then the shifted function $h - p$ is also logarithmically concave on $H$:
--
--   $$
--   h(\lambda x + (1-\lambda) y) - p \ \ge\ \bigl(h(x) - p\bigr)^{\lambda}\bigl(h(y) - p\bigr)^{1-\lambda}, \qquad x, y \in H,\ 0 < \lambda < 1 .
--   $$
--
--   Applied to $h = h_i$ and $p = p_i$, the theorem shows that each term $\ln\bigl((h_i(x) - p_i)/M_i\bigr)$ of the logarithmic penalty function (5.5) is concave, so the SUMT penalty function $T(x,s)$ is convex on the set where all constraints hold strictly.
--
--   **Formalization Note** Log-concavity is the platform predicate `ConvexOptimization.LogConcaveOn`, taken on the set $H$; it includes nonnegativity of the function on $H$ (for $h - p$ this is the definition of $H$) and the endpoint weights $\lambda \in \{0, 1\}$, which are trivial. Convexity of $H$ is a hypothesis, as in the book.
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, §5.2, p. 125, Theorem 5.2.1

import Mathlib
import Definitions.Def_LogConcaveOn

namespace NumStochOpt.LogConcave

theorem theorem_5_2_1_shifted_logconcave {n : ℕ}
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hH : Convex ℝ {x | p ≤ h x})
    (hlc : ConvexOptimization.LogConcaveOn {x | p ≤ h x} h) :
    ConvexOptimization.LogConcaveOn {x | p ≤ h x} (fun x => h x - p) := by sorry

end NumStochOpt.LogConcave
