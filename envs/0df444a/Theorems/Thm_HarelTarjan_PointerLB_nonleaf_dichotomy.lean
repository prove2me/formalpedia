-- Prove2me | Theorems.Thm_HarelTarjan_PointerLB_nonleaf_dichotomy
-- name    : HarelTarjan.PointerLB.nonleaf_dichotomy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:40:56.702767+00:00
-- url     : https://prove2.me/theorems/3dfa84a8-9951-464f-a8c5-88f17f9e5999
-- title:
--   Proof of Theorem 1 (p. 340) — a nonleaf $w$ lies in $A_x$ for all leaves below one of its children
-- statement:
--   Let $T$ be the complete binary tree of height $h$, represented in a list structure with two pointers per node by a map $\mathrm{rep}$ from vertices to nodes, and suppose that every nca query on two leaves is answered in $k$ steps. For a leaf $x$ let $A_x$ be the set of tree vertices whose nodes are accessible from $\mathrm{rep}(x)$ in $k$ steps or less.
--
--   Let $w$ be a nonleaf vertex of $T$, with children $u = w0$ and $v = w1$. Then either
--   $$w \in A_x \text{ for every leaf } x \text{ that is a descendant of } u, \quad\text{or}\quad w \in A_y \text{ for every leaf } y \text{ that is a descendant of } v.$$
--
--   This dichotomy is what forces every vertex to be seen from many leaves, and it drives the counting in the proof of Theorem 1.
--
--   **Formalization Note** The statement does not assume that $\mathrm{rep}$ is injective; the paper's representation is, and the claim holds without it.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 340, proof of Theorem 1, first paragraph ("We claim that either …")

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem nonleaf_dichotomy {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k)
    (w : Vertex h) (hw : w.1.length < h) :
    (∀ x : Vertex h, IsLeaf x → w.1 ++ [false] <+: x.1 → w ∈ A ptr rep k x) ∨
      (∀ y : Vertex h, IsLeaf y → w.1 ++ [true] <+: y.1 → w ∈ A ptr rep k y) := by sorry

end HarelTarjan.PointerLB
