-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_lowerBound_example
-- name    : JohnsonApprox.ExactCover.lowerBound_example
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:34:26.99497+00:00
-- url     : https://prove2.me/theorems/4ef846ce-634e-493c-a7ef-d48a756b898a
-- title:
--   Proof of Theorem 6 — on the filled-out Fig. 1 input, C2 may pay Σ_{j=1}^k (1/j) times F*
-- statement:
--   Let $k \ge 1$ and let $F$ be the lower-bound input of Theorem 6: Fig. 1's family ($k!$ disjoint sets $F_0$, one point per segment, and for each $j$ the $k!/j$ disjoint $j$-element sets of $F_1$ covering segment $j$), with every set of $F_1$ filled out with points of segment $k$ to exactly $k$ elements. Then
--
--   1. every set of $F$ has exactly $k$ elements, so $F \in EC(k)$;
--   2. $F^* > 0$;
--   3. some subcover $M$ is choosable by C2 on $F$ and
--   $$m_{EC}(M) \ge \Big(\sum_{j=1}^k \frac{1}{j}\Big)\, F^*.$$
--
--   It shows that the ratio of C2 on EC$(k)$ reaches $\sum_{j=1}^k 1/j$, so the upper bound $1 + \ln k$ of Theorem 6 is within $1/2$ of the truth.
--
--   **Formalization Note** The input is `lbInput k`; $\sum_{j=1}^k 1/j$ is Mathlib's `harmonic k` cast to the reals. The inequality is stated multiplicatively.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, proof of Theorem 6 (lower bound); pp. 265–266, Fig. 1

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2
import Definitions.Def_JohnsonApprox_ExactCover_LowerBoundInput

namespace JohnsonApprox.ExactCover

/-- Theorem 6, lower bound (p. 271): on the Fig. 1 input with every set of `F₁` filled out from
segment `k` to exactly `k` elements, C2 may choose a subcover of measure at least
`(Σ_{j=1}^k 1/j) · F*`. -/
theorem lowerBound_example (k : ℕ) (hk : 1 ≤ k) :
    (∀ i, ((lbInput k).S i).card = k) ∧ InEC k (lbInput k) ∧ 0 < (lbInput k).opt ∧
      ∃ M, Choosable (lbInput k) M ∧
        (harmonic k : ℝ) * (lbInput k).opt ≤ (lbInput k).measure M := by sorry

end JohnsonApprox.ExactCover
