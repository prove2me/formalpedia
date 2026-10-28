-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_lemma_4_2
-- name    : NonconvexCost.Complexity.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:44.557146+00:00
-- url     : https://prove2.me/theorems/68e2546d-4ada-405f-9b42-acc02313b9d0
-- title:
--   Lemma 4.2, p. 9 — the shortest vector in [g, g′] satisfies |g″|² ≤ |g|²(1 − |g|²/16L²)
-- statement:
--   Let $X$ be a real inner product space and $L>0$. Let $g,g'\in X$ lie in the closed ball $B_L(0)$, i.e. $|g|\le L$ and $|g'|\le L$, and suppose
--   $$\langle g',g\rangle\le\tfrac12|g|^2 .$$
--   Then every shortest vector $g''$ in the line segment $[g,g']$ satisfies
--   $$|g''|^2\le|g|^2\Big(1-\frac{|g|^2}{16L^2}\Big).$$
--
--   This is the shrinking step of Algorithm 4.1: each line search returns a $g'$ with $\langle g',g\rangle<\frac12|g|^2$, and replacing $g$ by the shortest vector in $[g,g']$ decreases $|g|^2$ by a definite factor.
--
--   **Formalization Note** "Shortest vector" is the predicate that $g''\in[g,g']$ has the least norm on the segment; $L>0$ is part of "$L$-bounded" on p. 2.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 9, Lemma 4.2

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

namespace NonconvexCost.Complexity

open scoped RealInnerProductSpace

theorem lemma_4_2 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L : ℝ) (hL : 0 < L) (g g' g'' : X) (hg : ‖g‖ ≤ L) (hg' : ‖g'‖ ≤ L)
    (hinner : ⟪g', g⟫ ≤ ‖g‖ ^ 2 / 2) (hshort : IsShortestIn g g' g'') :
    ‖g''‖ ^ 2 ≤ ‖g‖ ^ 2 * (1 - ‖g‖ ^ 2 / (16 * L ^ 2)) := by sorry

end NonconvexCost.Complexity
