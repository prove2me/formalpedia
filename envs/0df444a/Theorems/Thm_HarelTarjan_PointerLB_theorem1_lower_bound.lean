-- Prove2me | Theorems.Thm_HarelTarjan_PointerLB_theorem1_lower_bound
-- name    : HarelTarjan.PointerLB.theorem1_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:42:18.951558+00:00
-- url     : https://prove2.me/theorems/2236d8e8-7f19-4b67-98ce-ccefe104e82c
-- title:
--   Theorem 1 (explicit form proved on p. 341) — any pointer machine needs $k > \lg\lg n - 2$ steps per nca query
-- statement:
--   Let $T$ be a complete binary tree of height $h$ with $n = 2^h$ leaves. Let $T$ be represented in an arbitrary list structure: a collection $N$ of nodes, each with two pointer fields, and an injective map $\mathrm{rep}$ assigning to each tree vertex the node that represents it (other nodes may exist). Suppose that for every two leaves $x, y$ of $T$ some run of at most $k$ steps from the input nodes $\mathrm{rep}(x), \mathrm{rep}(y)$ holds a pointer to $\mathrm{rep}(\operatorname{nca}(x,y))$, where each step follows one pointer field of a node already held. Then
--   $$k > \lg\lg n - 2 .$$
--
--   This is the explicit form, proved on p. 341, of Harel and Tarjan's Theorem 1: any pointer machine requires $\Omega(\log\log n)$ time to answer an nca query in the worst case, independently of how the tree is represented. It shows that van Leeuwen's $O(\log\log n)$-per-query pointer-machine algorithm is optimal up to a constant factor, and separates pointer machines from random-access machines, on which the paper answers queries in $O(1)$ time.
--
--   **Formalization Note** $\lg = \log_2$ is `Real.logb 2`. For $h = 0$ Lean's convention $\log_2 0 = 0$ makes the claim read $k > -2$, which is true; for $h \ge 1$, $\lg\lg n = \log_2 h$ is the honest value. The list structure (`N`, `ptr`, `rep`) is universally quantified, which is "independent of the representation". The hypothesis concerns only queries on two leaves, which is weaker than all queries, so the theorem is at least as strong as the paper's. The paper's reduction of any fixed number of pointers per node to two is not formalized: the model has two pointer fields. Time is measured by pointer-following steps, each of which costs at least one unit of time on the machine.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 340, Theorem 1; explicit form k > lg lg n − 2 from the last display of its proof, p. 341

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem theorem1_lower_bound (h k : ℕ) {N : Type*} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hrep : Function.Injective rep)
    (hk : AnswersLeafQueriesIn ptr rep k) :
    Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ h)) - 2 < (k : ℝ) := by sorry

end HarelTarjan.PointerLB
