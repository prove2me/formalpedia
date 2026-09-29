-- Prove2me | Theorems.Thm_HarelTarjan_PointerLB_half_leaves_occurrences
-- name    : HarelTarjan.PointerLB.half_leaves_occurrences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:41:26.682264+00:00
-- url     : https://prove2.me/theorems/2e04717a-49a7-445e-8d9a-cda80ab37712
-- title:
--   Proof of Theorem 1 (p. 340) — a vertex of height $i \ge 1$ occurs in at least $2^{i-1}$ sets $A_x$
-- statement:
--   Let $T$ be the complete binary tree of height $h$, represented in a list structure with two pointers per node by a map $\mathrm{rep}$ from vertices to nodes, and suppose that every nca query on two leaves is answered in $k$ steps. For a leaf $x$ let $A_x$ be the set of tree vertices whose nodes are accessible from $\mathrm{rep}(x)$ in $k$ steps or less.
--
--   If $w$ is a vertex of height $i \ge 1$ (depth $h - i$), then $w$ belongs to $A_x$ for at least half of its $2^i$ leaf descendants $x$:
--   $$\bigl|\{\, x \in L : x \text{ is a descendant of } w,\ w \in A_x \,\}\bigr| \ge 2^{i-1},$$
--   where $L$ is the set of leaves of $T$.
--
--   **Formalization Note** The count is `Set.encard`. The height $i$ is fixed through $|w| + i = h$ with $1 \le i$, so $i - 1$ is not truncated. As in `nonleaf_dichotomy`, $\mathrm{rep}$ need not be injective.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 340, proof of Theorem 1, second paragraph, first two sentences

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem half_leaves_occurrences {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k)
    (w : Vertex h) (i : ℕ) (hi : 1 ≤ i) (hwi : w.1.length + i = h) :
    (2 ^ (i - 1) : ℕ∞) ≤
      {x : Vertex h | IsLeaf x ∧ IsAncestor w x ∧ w ∈ A ptr rep k x}.encard := by sorry

end HarelTarjan.PointerLB
