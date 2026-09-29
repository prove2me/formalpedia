-- Prove2me | Theorems.Thm_JohnsonApprox_SubsetSum_step1_big_dominates
-- name    : JohnsonApprox.SubsetSum.step1_big_dominates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:17:48.032024+00:00
-- url     : https://prove2.me/theorems/fad1b4d7-0e56-4be0-9abe-32387f8c3cd6
-- title:
--   Proof of Theorem 1: Step 1 makes m(T_1^BIG) ≥ m(T_0^BIG)
-- statement:
--   Let $k \ge 1$ and let $\langle T, s, b\rangle$ be a SUBSET-SUM input. For a set $X$ write $X^{\mathrm{BIG}} = \{x \in X : s(x) > b/(k+1)\}$. If $T_1$ is choosable by algorithm $A_k$ on this input and $T_0 \subseteq T$ is any approximate solution ($m(T_0) \le b$), then
--
--   $$m\big(T_1^{\mathrm{BIG}}\big) \;\ge\; m\big(T_0^{\mathrm{BIG}}\big).$$
--
--   In the paper this is the sentence "By Step 1 of algorithm $A_k$, $m(T_1^{\mathrm{BIG}}) \ge m(T_0^{\mathrm{BIG}})$", stated for an optimal solution $T_0$. It is the first half of the case analysis behind the upper bound of Theorem 1: the big elements selected by the algorithm are at least as heavy as those of any feasible solution.
--
--   **Formalization Note** The statement is made for every approximate solution $T_0$, not only an optimal one, which is stronger and is what the paper's argument gives. "Choosable" is the nondeterministic run relation of the definition of $A_k$, so the inequality holds for every tie-break in Steps 1 and 3.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 260, proof of Theorem 1

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem step1_big_dominates {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (u : Input α)
    (T₀ T₁ : Finset α) (hT₁ : Choosable k u T₁) (hT₀ : IsFeasible u T₀) :
    measure u (bigPart k u T₀) ≤ measure u (bigPart k u T₁) := by sorry

end JohnsonApprox.SubsetSum
