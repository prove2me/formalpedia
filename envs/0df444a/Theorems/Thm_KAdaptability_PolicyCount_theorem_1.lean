-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_theorem_1
-- name    : KAdaptability.PolicyCount.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T08:04:47.474992+00:00
-- url     : https://prove2.me/theorems/0541fb6e-3b56-4ade-81c6-b18d26855e3a
-- title:
--   Theorem 1 — min{dim 𝒴, rk Q} + 1 policies attain the optimal value of 𝒫𝒪
-- statement:
--   Consider a two-stage robust binary program $\mathcal{PO}$ with objective uncertainty: a nonempty bounded polyhedral uncertainty set $\Xi$, first-stage set $\mathcal X\subseteq\mathbb R^N_+$ and finite second-stage set $\mathcal Y\subseteq\{0,1\}^M$. Let $\dim\mathcal Y$ be the affine dimension of $\mathcal Y$ and $\operatorname{rk}Q$ the rank of the second-stage cost matrix $Q$. Then for every number of policies
--
--   $$K\ \ge\ \min\{\dim\mathcal Y,\ \operatorname{rk}Q\}+1,$$
--
--   the K-adaptability problem $\mathcal{PO}_K$ has the same optimal value as $\mathcal{PO}$:
--
--   $$\operatorname{opt}(\mathcal{PO}_K)=\operatorname{opt}(\mathcal{PO}).$$
--
--   Under objective uncertainty, a number of here-and-now policies that is at most linear in the dimension of the second-stage decisions, or in the rank of the cost matrix, therefore loses nothing compared with full second-stage adaptability, although $\mathcal Y$ may have exponentially many elements.
--
--   **Formalization Note** Optimal values are in `EReal` (infeasibility gives $+\infty$). The theorem is stated for every $K$ at or above the threshold. `Matrix.rank` equals the row rank. For $\mathcal Y=\emptyset$ the Lean affine dimension is $0$; both optimal values are then $+\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 12, Theorem 1

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_PO
import Definitions.Def_KAdaptability_PolicyCount_POK

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- Theorem 1, p. 12: the K-adaptability problem 𝒫𝒪_K has the same optimal value as the
two-stage robust binary program 𝒫𝒪 for every `K ≥ min{dim 𝒴, rk Q} + 1`. -/
theorem theorem_1 (P : Problem N M L nQ R) (K : ℕ)
    (hK : min P.dimY P.Q.rank + 1 ≤ K) :
    P.optPOK K = P.optPO := by sorry

end KAdaptability.PolicyCount
