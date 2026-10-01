-- Prove2me | Theorems.Thm_HadwigerConj_edge_bounds_small_complete_minors
-- name    : HadwigerConj.edge_bounds_small_complete_minors
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:48:25.198415+00:00
-- url     : https://prove2.me/theorems/18785bfe-b6c9-42a1-9313-0070c6d785f8
-- title:
--   Exact edge bounds for graphs with no $K_3$, $K_4$ or $K_5$ minor
-- statement:
--   Let $G$ be a finite graph with $n$ vertices.
--
--   1. If $n\ge 1$ and $G$ has no $K_3$ minor, then $|E(G)|\le n-1$.
--   2. If $n\ge 2$ and $G$ has no $K_4$ minor, then $|E(G)|\le 2n-3$.
--   3. If $n\ge 3$ and $G$ has no $K_5$ minor, then $|E(G)|\le 3n-6$.
--
--   These are the cases $t\le 5$ of the extremal function for $K_t$ minors, and they are sharp.
--
--   **Formalization Note** The bounds are written additively in the natural numbers, e.g. $|E(G)|+3\le 2n$, to avoid truncated subtraction.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 3, the three bullet points after Theorem 3.2 (p. 4)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem edge_bounds_small_complete_minors {V : Type} [Finite V] (G : SimpleGraph V) :
    (1 ≤ Nat.card V → ¬ HasCompleteMinor G 3 → G.edgeSet.ncard + 1 ≤ Nat.card V) ∧
    (2 ≤ Nat.card V → ¬ HasCompleteMinor G 4 → G.edgeSet.ncard + 3 ≤ 2 * Nat.card V) ∧
    (3 ≤ Nat.card V → ¬ HasCompleteMinor G 5 → G.edgeSet.ncard + 6 ≤ 3 * Nat.card V) := by sorry
end HadwigerConj
