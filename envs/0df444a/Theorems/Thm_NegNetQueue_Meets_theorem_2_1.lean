-- Prove2me | Theorems.Thm_NegNetQueue_Meets_theorem_2_1
-- name    : NegNetQueue.Meets.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:23.31375+00:00
-- url     : https://prove2.me/theorems/9ac43481-6f11-45c6-bec4-c1fc76af0ee4
-- title:
--   Theorem 2 (1), p. 9 — X_j is distributed as row j of A^j, and M_j = j − 1 + X_j accordingly
-- statement:
--   Let $\varepsilon$ be an event sequence of an M/M/c/n queue and $q=c\mu/(\lambda+c\mu)$. For a customer arriving at position $j$, $1\le j\le n$, let $X_j$ be the number of later arrivals she meets before entering service and $M_j=j-1+X_j$ the total number of waiting customers she meets. Then for every $i\in\{0,\dots,n\}$,
--   $$P(X_j=i)=(A^j)(j,i),\qquad P(M_j=j-1+i)=(A^j)(j,i).$$
--
--   This expresses the exposure of a joining customer through powers of the explicit matrix $A$ of (2); Theorem 3 gives the same law in closed form.
--
--   **Formalization Note.** $X_j$ is valued in $\mathbb N\cup\{\infty\}$ (it is at most $n$ everywhere); the row index $j$ is the element $\langle j,\cdot\rangle$ of $\{0,\dots,n\}$.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), p. 9, Theorem 2 (1)

import Mathlib
import Definitions.Def_NegNetQueue_Meets_EventSeq
import Definitions.Def_NegNetQueue_Meets_Model

namespace NegNetQueue.Meets

open MeasureTheory ProbabilityTheory

/-- Theorem 2 (1), p. 9: for a customer arriving at position `j` (`1 ≤ j ≤ n`) of an M/M/c/n queue,
`X_j` has law row `j` of `A^j`, and `M_j = j - 1 + X_j` has that law shifted by `j - 1`. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) (ε : ℕ → Ω → Bool)
    (hε : IsEventSeq P lam mu c ε) (n : ℕ) :
    ∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) (i : Fin (n + 1)),
      (P {ω | Xmet n j ε ω = ((i : ℕ) : ℕ∞)}).toReal =
          (Amat n (qComp lam mu c) ^ j) ⟨j, Nat.lt_succ_of_le hjn⟩ i ∧
      (P {ω | Mmeet n j ε ω = ((j - 1 + (i : ℕ) : ℕ) : ℕ∞)}).toReal =
          (Amat n (qComp lam mu c) ^ j) ⟨j, Nat.lt_succ_of_le hjn⟩ i := by sorry

end NegNetQueue.Meets
