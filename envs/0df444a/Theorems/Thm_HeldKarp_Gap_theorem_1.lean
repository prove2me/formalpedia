-- Prove2me | Theorems.Thm_HeldKarp_Gap_theorem_1
-- name    : HeldKarp.Gap.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:19.249153+00:00
-- url     : https://prove2.me/theorems/a4ef41d9-6f9b-4bd0-b9e3-60b92dc7e588
-- title:
--   Theorem 1 — the extreme points of $A'x\le b'$, $x\ge 0$ are the incidence vectors of the 1-trees
-- statement:
--   Let $n\ge 3$ and let $T^1,\dots,T^q$ be the 1-trees on the vertex set $\{1,2,\dots,n\}$. Associate with $T^k$ the $\binom n2$-vector $(e^k_{ij})$ with $e^k_{ij}=1$ if $\{i,j\}$ is an edge of $T^k$ and $0$ otherwise. Let $P$ be the polyhedron $A'x\le b'$, $x\ge 0$ of real $\binom n2$-vectors defined by
--
--   $$
--   \sum_j x_{1j}=2,\qquad \sum_{1\le i<j\le n}x_{ij}=n,\qquad \sum_{i\in S,\,j\in S,\,i<j}x_{ij}\le |S|-1\ \ (\emptyset\ne S\subsetneq\{2,\dots,n\}),\qquad 0\le x_{ij}\le 1.
--   $$
--
--   Then the extreme points of $P$ are exactly the points $(e^k_{ij})$, $k=1,\dots,q$.
--
--   The theorem identifies $P$ as the convex hull of the 1-trees, so a linear program over $P$ is a minimum 1-tree problem; it is the bridge between the gap function and linear programming.
--
--   **Formalization Note** $\sum_j x_{1j}=2$ and $\sum x_{ij}=n$ are equalities as printed in (3′); the shorthand "$A'x\le b'$" is not read literally (then $x=0$ would be an extreme point). Subsets $S$ are nonempty. Vectors live in the space of functions on unordered pairs $\{i,j\}$, $i\ne j$, of `Fin n` (vertex $1$ is `0`), and extreme points are taken in that real vector space. 1-trees are the published `HeldKarp.Ascent.IsOneTree`.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1144, §2, Theorem 1

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **Theorem 1** (Held & Karp 1970, §2, p. 1144). The extreme points of the polyhedron
`A′x ≤ b′, x ≥ 0` are exactly the incidence vectors `(e^k_ij)` of the 1-trees `T^k` on the vertex
set `{1, 2, …, n}`. -/
theorem theorem_1 {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    Set.extremePoints ℝ (OneTreePolyhedron n) =
      incidence '' {G : SimpleGraph (Fin n) | IsOneTree G} := by sorry

end HeldKarp.Gap
