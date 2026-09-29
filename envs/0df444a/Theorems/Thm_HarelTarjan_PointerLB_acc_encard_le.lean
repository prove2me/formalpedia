-- Prove2me | Theorems.Thm_HarelTarjan_PointerLB_acc_encard_le
-- name    : HarelTarjan.PointerLB.acc_encard_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:40:13.839818+00:00
-- url     : https://prove2.me/theorems/5f8e1f4b-492e-4c3f-ba08-3cdcba81008f
-- title:
--   Proof of Theorem 1 (p. 340) — at most $2^{j+1}-1$ nodes are accessible in $j$ steps or less
-- statement:
--   Consider a list structure on an arbitrary (possibly infinite) collection of nodes, in which every node has two pointer fields, each containing a node or nil. For every node $a$ and every $j \ge 0$, the set $\mathrm{acc}_j(a)$ of nodes accessible from $a$ in $j$ steps or less is finite and
--   $$|\mathrm{acc}_j(a)| \le 2^{j+1} - 1.$$
--
--   This is "the key point" of the proof of Theorem 1: a pointer machine that has followed $j$ pointers from a node can have seen only exponentially many nodes in $j$.
--
--   **Formalization Note** The cardinality is `Set.encard`, valued in $\mathbb N \cup \{\infty\}$, so the inequality also asserts finiteness. It is written as $|\mathrm{acc}_j(a)| + 1 \le 2^{j+1}$ to avoid truncated subtraction.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 340, proof of Theorem 1, first paragraph, second sentence

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem acc_encard_le {N : Type*} (ptr : N → Fin 2 → Option N) (a : N) (j : ℕ) :
    (acc ptr j a).encard + 1 ≤ 2 ^ (j + 1) := by sorry

end HarelTarjan.PointerLB
