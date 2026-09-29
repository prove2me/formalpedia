-- Prove2me | Theorems.Thm_JohnsonApprox_SubsetSum_lowerBoundInput_spec
-- name    : JohnsonApprox.SubsetSum.lowerBoundInput_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:19:12.431055+00:00
-- url     : https://prove2.me/theorems/4725d5ff-50eb-415a-8f9e-2fbdcfdc5bbd
-- title:
--   Proof of Theorem 1: on the lower-bound input, ⟨T, s, b⟩* = k + 1 and A_k(⟨T, s, b⟩) = k + ε
-- statement:
--   Let $k \ge 1$ and $0 < \varepsilon < 1$, and consider the input $\langle T, s, b\rangle$ with $T = \{a_1, \dots, a_{k+2}\}$, $s(a_1) = 1 + \varepsilon$, $s(a_i) = 1$ for $i \ge 2$, and $b = k + 1$. Then:
--
--   1. the optimal measure is $\langle T, s, b\rangle^* = k + 1$;
--   2. every set $T_1$ choosable by $A_k$ on this input has measure $m(T_1) = k + \varepsilon$;
--   3. at least one set is choosable by $A_k$ on this input.
--
--   Parts 2 and 3 together say that the performance of $A_k$ on this input, the worst measure over its choosable outputs, is
--
--   $$A_k(\langle T, s, b\rangle) = k + \varepsilon, \qquad\text{so}\qquad r(A_k, \langle T, s, b\rangle) = \frac{k+1}{k+\varepsilon}.$$
--
--   Letting $\varepsilon \to 0$ shows that the constant $(k+1)/k$ of Theorem 1 is the best possible.
--
--   **Formalization Note** The input is `lowerBoundInput k ε hε` on `Fin (k + 2)`. The paper takes $\varepsilon$ small without stating a range; $\varepsilon < 1$ is needed so that $a_1$ fits into the bound when $k = 1$ ($1 + \varepsilon \le k + 1$) and so that exactly $k - 1$ elements of size $1$ are added after $a_1$. Part 3 rules out the vacuous reading of part 2.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 261, proof of Theorem 1

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak
import Definitions.Def_JohnsonApprox_SubsetSum_LowerBoundInput

namespace JohnsonApprox.SubsetSum

theorem lowerBoundInput_spec (k : ℕ) (hk : 1 ≤ k) (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    opt (lowerBoundInput k ε hε) = (k : ℚ) + 1 ∧
      (∀ T₁, Choosable k (lowerBoundInput k ε hε) T₁ →
        measure (lowerBoundInput k ε hε) T₁ = (k : ℚ) + ε) ∧
      ∃ T₁, Choosable k (lowerBoundInput k ε hε) T₁ := by sorry

end JohnsonApprox.SubsetSum
