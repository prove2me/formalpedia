-- Prove2me | Theorems.Thm_HadwigerConj_mader_edge_bound_le_seven
-- name    : HadwigerConj.mader_edge_bound_le_seven
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:51:45.926874+00:00
-- url     : https://prove2.me/theorems/3ebb84d5-7637-4797-9fcc-79efaac9d260
-- title:
--   Theorem 3.3 (Mader): for $t\le 7$, no $K_t$ minor $\Rightarrow$ $|E|\le (t-2)n-\binom{t-1}{2}$
-- statement:
--   Let $t\le 7$ and let $G$ be a finite graph with $n$ vertices, where $n\ge t-2$. If $G$ has no $K_t$ minor, then
--
--   $$|E(G)|\le (t-2)\,n-\frac{(t-1)(t-2)}{2}.$$
--
--   The bound is attained by $K_{t-2}$ joined completely to an independent set of $n-t+2$ vertices; for $t\ge 8$ the formula fails ($K_{2,2,2,2,2}$ has no $K_8$ minor).
--
--   **Formalization Note** The inequality is stated in the integers; $(t-1)(t-2)$ is always even, so the integer division is exact.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Theorem 3.3 (p. 5)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem mader_edge_bound_le_seven (t : ℕ) (ht : t ≤ 7) {V : Type} [Finite V]
    (G : SimpleGraph V) (hn : (t : ℤ) - 2 ≤ Nat.card V) (hG : ¬ HasCompleteMinor G t) :
    (G.edgeSet.ncard : ℤ) ≤ ((t : ℤ) - 2) * Nat.card V - ((t : ℤ) - 1) * ((t : ℤ) - 2) / 2 := by sorry
end HadwigerConj
