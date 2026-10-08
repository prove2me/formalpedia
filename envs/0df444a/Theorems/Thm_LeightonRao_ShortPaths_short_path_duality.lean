-- Prove2me | Theorems.Thm_LeightonRao_ShortPaths_short_path_duality
-- name    : LeightonRao.ShortPaths.short_path_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:11.83798+00:00
-- url     : https://prove2.me/theorems/6ddc84a5-7bf3-44f9-86f1-9ff7cf681c4c
-- title:
--   §2.5, p. 808 — linear-programming duality for short-path UMFP
-- statement:
--   Let $N$ be a connected finite network with at least two vertices, and let $L$ be a hop limit. Write $F_L$ for the maximum uniform concurrent flow routed on paths of at most $L$ edges. For a nonnegative symmetric distance function $d$, write $W(d)=\sum_e C(e)d(e)$ and let $d_L(u,v)$ be the shortest distance among paths with at most $L$ edges, allowing $\infty$ when none exists. Then every such $d$ satisfying the restricted distance constraint
--
--   $$\frac12\sum_{u,v\in V}d_L(u,v)\ge1$$
--
--   has $F_L\le W(d)$.
--
--   For $L>0$, a feasible flow attains $F_L$, and a feasible distance function has $W(d)=F_L$. Thus the restricted dual has the same optimum as the short-path flow problem.
--
--   **Formalization Note** The paper gives the dual in prose on p. 808. The dual equality and both attainment claims are the finite linear-programming reading of that sentence. An unavailable path contributes $\infty$, as the paper explicitly notes.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 808, §2.5, short-path LP duality paragraph

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- The LP dual for the hop-restricted uniform multicommodity flow problem, §2.5, p. 808. -/
theorem short_path_duality {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) (L : ℕ) :
    (∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesShortConstraint N d L →
      maxShortFlow N uniformDemand L ≤ totalWeight N d) ∧
    (0 < L → ∃ f : V → V → ℕ → V → V → ℝ,
      IsShortConcurrentFlow N uniformDemand L f (maxShortFlow N uniformDemand L)) ∧
    (0 < L → ∃ d : V → V → ℝ, IsDistanceFunction d ∧
      SatisfiesShortConstraint N d L ∧
      totalWeight N d = maxShortFlow N uniformDemand L) := by sorry

end LeightonRao.ShortPaths
