-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_ec2_rank
-- name    : KAdaptability.PolicyCount.ec2_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:03:36.932201+00:00
-- url     : https://prove2.me/theorems/ba7b92fe-138d-4ed3-ac34-3dfe44044ad1
-- title:
--   Proof of Theorem 1, case rk Q < dim 𝒴, p. ec2 — rk Q + 1 randomized policies suffice
-- statement:
--   Let $\operatorname{rk}Q$ be the rank of the second-stage cost matrix $Q$. Problem (EC.1), which mixes $|\mathcal Y|$ policies with weights in $\Delta_{|\mathcal Y|}$, has the same optimal value as the analogous problem that mixes $\operatorname{rk}Q+1$ policies with weights in $\Delta_{\operatorname{rk}Q+1}$:
--
--   $$\operatorname{opt}(\text{EC.1 with }|\mathcal Y|\text{ policies})=\operatorname{opt}(\text{EC.1 with }\operatorname{rk}Q+1\text{ policies}).$$
--
--   This is the case $\operatorname{rk}Q<\dim\mathcal Y$ of Theorem 1, which the paper treats "analogously" to the claim (EC.1) = (EC.2).
--
--   **Formalization Note** Both sides are `optMixed` in `EReal`. `Matrix.rank` is the rank of $Q$ as a linear map, which equals its row rank. The statement is made without the case assumption $\operatorname{rk}Q<\dim\mathcal Y$, which the claim does not need.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec2 (PDF p. 36), Proof of Theorem 1, last sentence (case rk Q < dim 𝒴)

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Mixed

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- Proof of Theorem 1, case `rk Q < dim 𝒴`, p. ec2: (EC.1) with `K = |𝒴|` policies has the
same optimal value as the analogue of (EC.2) with `rk Q + 1` policies. -/
theorem ec2_rank (P : Problem N M L nQ R) :
    P.optMixed P.Y.card = P.optMixed (P.Q.rank + 1) := by sorry

end KAdaptability.PolicyCount
