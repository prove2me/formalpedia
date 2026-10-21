-- Prove2me | Theorems.Thm_HeldKarp_Gap_feasible_3_tours
-- name    : HeldKarp.Gap.feasible_3_tours
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:58.446902+00:00
-- url     : https://prove2.me/theorems/589c6098-cf6f-4104-8569-866e3b734806
-- title:
--   §2, p. 1143 — the feasible solutions of the integer program (3) are the tours
-- statement:
--   Let $n\ge 3$. The feasible solutions of the integer program (3),
--
--   $$
--   \begin{aligned}
--   &\textstyle\sum_{j>i}x_{ij}+\sum_{j<i}x_{ji}=2 \quad (i=1,\dots,n),\\
--   &\textstyle\sum_{i\in S,\,j\in S,\,i<j}x_{ij}\le |S|-1 \quad \text{for every nonempty proper } S\subset\{2,\dots,n\},\\
--   &0\le x_{ij}\le 1,\qquad x_{ij}\ \text{integer},
--   \end{aligned}
--   $$
--
--   are in one-to-one correspondence with the tours of $K_n$: the map sending a tour to its incidence vector (the $\binom n2$-vector with $x_{ij}=1$ if $\{i,j\}$ is an edge of the tour and $0$ otherwise) is a bijection from the set of tours onto the set of feasible solutions of (3). In particular, the tour corresponding to a feasible solution $(x_{ij})$ includes the edge $\{i,j\}$ if and only if $x_{ij}=1$.
--
--   This is the classical integer-programming formulation of the traveling-salesman problem on which §2 builds.
--
--   **Formalization Note** Vectors are functions on the unordered pairs $\{i,j\}$, $i\neq j$, of `Fin n` (vertex $1$ is `0`). The subtour constraint is imposed for nonempty $S$ only; for $S=\emptyset$ it would read $0\le-1$. A tour is the published `HeldKarp.Ascent.IsTour`. The correspondence is stated as `Set.BijOn` of the incidence-vector map.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1143, §2 — the feasible solutions of program (3) (pp. 1141–1142) are in one-to-one correspondence with the tours

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **§2, p. 1143 — the feasible solutions of (3) are the tours** (Held & Karp 1970). The map
sending a graph to its incidence vector is a bijection from the tours of `K_n` onto the feasible
solutions of the integer program (3). -/
theorem feasible_3_tours {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    Set.BijOn (incidence (n := n)) {H : SimpleGraph (Fin n) | IsTour H}
      {x : Edge n → ℝ | Feasible3 x} := by sorry

end HeldKarp.Gap
