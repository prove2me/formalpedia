-- Prove2me | Theorems.Thm_JohnsonApprox_SetCover_fig1_run
-- name    : JohnsonApprox.SetCover.fig1_run
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:28:33.587524+00:00
-- url     : https://prove2.me/theorems/ef1e3ffd-4deb-4b39-81c0-9104d9156518
-- title:
--   Proof of Theorem 4 (Fig. 1) — C1 can choose F₁ with k!·Σ_{j=1}^k (1/j) sets while F* = k!
-- statement:
--   Let $k \ge 1$ and let $F$ be the input of Fig. 1: $k \cdot k!$ points in $k$ segments of $k!$ points, the subfamily $F_0$ of $k!$ disjoint $k$-element sets with one point per segment, and the subfamily $F_1$ made of $k!/j$ disjoint $j$-element sets covering segment $j$, for $j = 1, \dots, k$. Then:
--
--   1. $F$ is an input of $SC(k)$: no set has more than $k$ elements.
--   2. $F_0$ is a subcover of $F$, and the optimal measure is $F^* = k!$.
--   3. $F_1$ is choosable by algorithm C1 given $F$.
--   4. $F_1$ has
--   $$|F_1| = k! \sum_{j=1}^{k} \frac{1}{j}$$
--   sets.
--
--   Consequently $r(C1, F) \ge \sum_{j=1}^k (1/j)$, which shows that the upper bound of Theorem 4 is attained for every $k$.
--
--   **Formalization Note** The instance is the definition `fig1 k` (0-based segments). $F^* = k!$ is stated as an equality with `opt`, the minimum over all subcovers. The count is a rational equality with Mathlib's `harmonic k`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), pp. 265–266, proof of Theorem 4 (Fig. 1)

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Fig1

namespace JohnsonApprox.SetCover

theorem fig1_run (k : ℕ) (hk : 1 ≤ k) :
    InSC k (fig1 k) ∧ fig1F₀ k ∈ subcovers (fig1 k) ∧ opt (fig1 k) = k.factorial ∧
      Choosable (fig1 k) (fig1F₁ k) ∧
      ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k := by sorry

end JohnsonApprox.SetCover
