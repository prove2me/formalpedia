-- Prove2me | Theorems.Thm_HarelTarjan_PointerLB_sum_card_A_ge
-- name    : HarelTarjan.PointerLB.sum_card_A_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:41:46.541245+00:00
-- url     : https://prove2.me/theorems/f73ca5fe-ba0a-4218-9271-5210f572986e
-- title:
--   Proof of Theorem 1 (pp. 340–341) — $\sum_{x \in L} |A_x| \ge \frac{n}{2}\lg n$
-- statement:
--   Let $T$ be the complete binary tree of height $h$ with $n = 2^h$ leaves, represented in a list structure with two pointers per node by a map $\mathrm{rep}$ from vertices to nodes, and suppose that every nca query on two leaves is answered in $k$ steps. For a leaf $x$ let $A_x$ be the set of tree vertices whose nodes are accessible from $\mathrm{rep}(x)$ in $k$ steps or less, and let $L$ be the set of leaves. Then
--   $$\sum_{x \in L} |A_x| \ge \frac{n}{2} \lg n, \qquad\text{that is,}\qquad 2 \sum_{x \in L} |A_x| \ge h\, 2^h .$$
--
--   This double count of the occurrences of vertices in the sets $A_x$ is the lower half of the proof of Theorem 1; the upper half is the accessibility count $|A_x| < 2^{k+1}$.
--
--   **Formalization Note** With $n = 2^h$ one has $\lg n = h$, and the inequality is stated as $h \cdot 2^h \le 2 \sum_{x \in L} |A_x|$ in $\mathbb N \cup \{\infty\}$ (cardinalities are `Set.encard`), cleared of the division by $2$. $\mathrm{rep}$ need not be injective.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), pp. 340–341, proof of Theorem 1, second paragraph and first display on p. 341

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem sum_card_A_ge {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k) :
    (h : ℕ∞) * 2 ^ h ≤ 2 * ∑ x ∈ leaves h, (A ptr rep k x).encard := by sorry

end HarelTarjan.PointerLB
