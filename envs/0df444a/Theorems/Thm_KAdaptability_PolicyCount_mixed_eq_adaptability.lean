-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_mixed_eq_adaptability
-- name    : KAdaptability.PolicyCount.mixed_eq_adaptability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:02.513208+00:00
-- url     : https://prove2.me/theorems/ce8b3a6d-603f-4714-8c18-1238d38e1255
-- title:
--   Proof of Theorem 1, p. ec2 — (EC.2) is the (D+1)-adaptability problem
-- statement:
--   For every number $K$ of policies, the randomized-policy problem
--
--   $$\min\Big\{\max_{\xi\in\Xi}\Big[\xi^\top Cx+\sum_{k\in\mathcal K}\lambda_k\cdot\xi^\top Qy^k\Big] : x\in\mathcal X,\ y^k\in\mathcal Y,\ Tx+Wy^k\le h\ \forall k,\ \lambda\in\Delta_K\Big\}$$
--
--   has the same optimal value as the K-adaptability problem $\mathcal{PO}_K$. At $K=\dim\mathcal Y+1$ this identifies (EC.2) with the $(D+1)$-adaptability problem, and at $K=|\mathcal Y|$ it is the equivalence of $\mathcal{PO}_K$ and (EC.1).
--
--   **Formalization Note** The statement is the equality `optMixed K = optPOK K` of optimal values in `EReal`, for every $K\in\mathbb N$; the per-decision identity behind it is the milestone on (EC.1).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec2 (PDF p. 36), Proof of Theorem 1, reformulation of (EC.2) as the (D+1)-adaptability problem

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Mixed

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- Proof of Theorem 1, p. ec2: the mixed problem (EC.1)/(EC.2) with `K` policies has the same
optimal value as the K-adaptability problem 𝒫𝒪_K. -/
theorem mixed_eq_adaptability (P : Problem N M L nQ R) (K : ℕ) :
    P.optMixed K = P.optPOK K := by sorry

end KAdaptability.PolicyCount
