-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_card_policies_eq
-- name    : KAdaptability.PolicyCount.card_policies_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:03:36.194538+00:00
-- url     : https://prove2.me/theorems/03952e28-1111-4429-9fd8-d7b87f83ba0e
-- title:
--   Proof of Theorem 1, p. ec1 — with K = |𝒴| policies, 𝒫𝒪_K has the optimal value of 𝒫𝒪
-- statement:
--   The set $\mathcal Y\subseteq\{0,1\}^M$ is finite. With $K=|\mathcal Y|$ policies, the K-adaptability problem has the same optimal value as the two-stage robust binary program:
--
--   $$\operatorname{opt}(\mathcal{PO}_{|\mathcal Y|})=\operatorname{opt}(\mathcal{PO}).$$
--
--   This is the starting point of the proof of Theorem 1: with as many policies as there are second-stage decisions, every feasible second-stage decision can be listed among the policies.
--
--   **Formalization Note** Optimal values are in `EReal`. The statement holds without the case assumption $\dim\mathcal Y\le\operatorname{rk}Q$ that precedes it in the paper's proof. If $\mathcal Y=\emptyset$ both sides are $+\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec1 (PDF p. 35), Proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_PO
import Definitions.Def_KAdaptability_PolicyCount_POK

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- Proof of Theorem 1, p. ec1: with `K = |𝒴|` policies, 𝒫𝒪_K has the same optimal value as 𝒫𝒪. -/
theorem card_policies_eq (P : Problem N M L nQ R) :
    P.optPOK P.Y.card = P.optPO := by sorry

end KAdaptability.PolicyCount
