-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_hitIndices_card_le
-- name    : LenstraIP.Hyperplanes.hitIndices_card_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:35.184237+00:00
-- url     : https://prove2.me/theorems/0906eec9-3cd7-4e0d-afce-530f8927e350
-- title:
--   §1, p. 541 — if precisely t of the hyperplanes H + kbₙ meet B(p, R), then t − 1 ≤ 2R/h
-- statement:
--   Let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$ ($n \ge 1$), $H = \sum_{i=1}^{n-1}\mathbb R b_i$, and $h$ the distance of $b_n$ to $H$. The lattice $L = \sum_i \mathbb Z b_i$ lies in the union of the parallel hyperplanes $H + kb_n$, $k \in \mathbb Z$, which have successive distances $h$ from each other. Let $p \in \mathbb R^n$ and $R > 0$. Then only finitely many of these hyperplanes meet the closed ball $B(p, R)$, and if precisely $t$ of them do,
--   $$t - 1 \le \frac{2R}{h}.$$
--
--   Combined with the lower bound on $h$ in (12) and the radius bound $r < \frac12\sqrt n|b_n|$, this gives the goal theorem's count $t - 1 < c_1c_2\sqrt n$.
--
--   **Formalization Note** The set of indices is $\{k \in \mathbb Z : (H + kb_n) \cap B(p,R) \neq \emptyset\}$ (`hitIndices b p R`, the integer called `j` in Lean), and $t$ is its cardinality as a real number, so $t - 1$ is real subtraction. The paper says "suppose that precisely $t$ … intersect"; the Lean makes the finiteness of the set part of the conclusion, because `Set.ncard` of an infinite set is $0$. $R > 0$ is the paper's convention for balls. $n = k+1$, $b_n$ is `b (Fin.last k)`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, p. 541, 'Then we have clearly t − 1 ≤ 2R/h'

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, p. 541: if precisely `t` of the hyperplanes `H + j·bₙ` (`j ∈ ℤ`) meet
`B(p, R)`, then `t − 1 ≤ 2R/h`. The finiteness of the set of such `j` is part of the claim. -/
theorem hitIndices_card_le (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) (p : EuclideanSpace ℝ (Fin (k + 1))) (R : ℝ) (hR : 0 < R) :
    (hitIndices b p R).Finite ∧ ((hitIndices b p R).ncard : ℝ) - 1 ≤ 2 * R / hgt b := by sorry

end LenstraIP.Hyperplanes
