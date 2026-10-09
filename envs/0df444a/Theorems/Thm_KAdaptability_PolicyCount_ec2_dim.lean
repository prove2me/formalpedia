-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_ec2_dim
-- name    : KAdaptability.PolicyCount.ec2_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:03:49.367984+00:00
-- url     : https://prove2.me/theorems/35526daa-0ce9-4d93-909e-7eb5836bf51d
-- title:
--   Proof of Theorem 1, (EC.1) = (EC.2), p. ec2 — dim 𝒴 + 1 randomized policies suffice
-- statement:
--   Let $D=\dim\mathcal Y$ be the affine dimension of $\mathcal Y$. Problem (EC.1), which mixes $K=|\mathcal Y|$ policies with weights $\lambda\in\Delta_{|\mathcal Y|}$, has the same optimal value as problem (EC.2), which mixes $D+1$ policies with weights $\lambda\in\Delta_{D+1}$:
--
--   $$\operatorname{opt}(\text{EC.1})=\operatorname{opt}(\text{EC.2}).$$
--
--   Together with the min-max reformulation, this reduces $|\mathcal Y|$ policies to $\dim\mathcal Y+1$ policies, which is the case $\dim\mathcal Y\le\operatorname{rk}Q$ of Theorem 1.
--
--   **Formalization Note** Both sides are `optMixed` in `EReal`, at $K=|\mathcal Y|$ and $K=D+1$ policies; the policies need not be distinct.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec2 (PDF p. 36), Proof of Theorem 1, claim that (EC.1) and (EC.2) have the same optimal value

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Mixed

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- Proof of Theorem 1, claim (EC.1) = (EC.2), p. ec2: (EC.1) with `K = |𝒴|` policies has the
same optimal value as (EC.2) with `D + 1` policies, where `D = dim 𝒴`. -/
theorem ec2_dim (P : Problem N M L nQ R) :
    P.optMixed P.Y.card = P.optMixed (P.dimY + 1) := by sorry

end KAdaptability.PolicyCount
