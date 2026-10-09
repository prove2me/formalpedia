-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_conservative_approximation
-- name    : KAdaptability.PolicyCount.conservative_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:03:03.789349+00:00
-- url     : https://prove2.me/theorems/ce777b50-6e5d-446c-b705-3f340bccc92e
-- title:
--   §2, p. 12 — 𝒫𝒪_K is a conservative approximation of 𝒫𝒪
-- statement:
--   For every number $K$ of policies, the K-adaptability problem $\mathcal{PO}_K$ is a conservative approximation of the two-stage robust binary program $\mathcal{PO}$: its optimal value bounds that of $\mathcal{PO}$ from above,
--
--   $$\operatorname{opt}(\mathcal{PO})\ \le\ \operatorname{opt}(\mathcal{PO}_K).$$
--
--   This inequality is the easy half of Theorem 1; it also shows that once $\mathcal{PO}_K$ attains the optimal value of $\mathcal{PO}$ for some $K$, adding policies cannot change it.
--
--   **Formalization Note** Both optimal values are in `EReal`. The statement is made for every $K\in\mathbb N$; for $K=0$ the right-hand side is $+\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 12, paragraph before Theorem 1

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_PO
import Definitions.Def_KAdaptability_PolicyCount_POK

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- §2, p. 12: 𝒫𝒪_K is a conservative approximation of 𝒫𝒪 — for every number `K` of policies,
the optimal value of 𝒫𝒪_K is at least that of 𝒫𝒪. -/
theorem conservative_approximation (P : Problem N M L nQ R) (K : ℕ) :
    P.optPO ≤ P.optPOK K := by sorry

end KAdaptability.PolicyCount
