-- Prove2me | Theorems.Thm_MCPoise_theorem_2_8
-- name    : MCPoise.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:03.195955+00:00
-- url     : https://prove2.me/theorems/bf02c8ae-d52d-4d44-b043-4a337d330e87
-- title:
--   Theorem 2.8 (Cherkassky–Lovász) — an $S$-path-packing of size $\frac12 \sum_{t \in S} \lambda(t, S \setminus t)$
-- statement:
--   Let $M$ be a multigraph on a finite vertex set $V$ and let $S \subseteq V$.
--
--   **Theorem 2.8.** If every vertex in $V \setminus S$ has even degree, there is an $S$-path-packing of size
--   $$\frac12 \sum_{t \in S} \lambda(t, S \setminus t),$$
--   where $\lambda(t, S \setminus t)$ is the size of the minimum cut separating $t$ from $S \setminus t$.
--
--   The paper uses it to split the fractional flows of a group into paths between terminals.
--
--   Differences from the source:
--   - encoding: a graph with vertex set V; λ(t, S \ t) the min-cut size → a finite multigraph as a list of edges; λ the minimum over vertex sets W ∋ t disjoint from S \ t; reason: the theorem is applied to a finite multigraph (p.17), and these are its cuts
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 2.8, Definition 4, p.17

import Mathlib
import Definitions.Def_MCPoise_MGraph

namespace MCPoise

/-- **Theorem 2.8 (Cherkassky–Lovász).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 2.8, p.17: "If every vertex in V \ S has even degree, then there exists an S-path-packing of size ½ Σ_{t∈S} λ(t, S \ t), where λ(t, S \ t) is the
size of the min-cut separating t from S \ t. (Note that this is the maximum possible size of such a packing, since each t ∈ S can be an endpoint of at most
λ(t, S \ t) edge-disjoint paths.)"

The page's parenthetical is a remark and is not part of the statement. -/
theorem theorem_2_8 {V : Type*} [Fintype V] [DecidableEq V] (M : MGraph V) (S : Finset V)
    (h : ∀ v, v ∉ S → Even (M.deg v)) :
    ∃ Q : List (MPath V), IsSPacking M S Q ∧
      2 * Q.length = ∑ t ∈ S, M.lam t (S.erase t) := by sorry

end MCPoise
