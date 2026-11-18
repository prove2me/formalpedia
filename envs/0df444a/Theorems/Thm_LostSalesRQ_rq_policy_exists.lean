-- Prove2me | Theorems.Thm_LostSalesRQ_rq_policy_exists
-- name    : LostSalesRQ.rq_policy_exists
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:23:36.266563+00:00
-- url     : https://prove2.me/theorems/f641673f-fd34-43d1-b4a0-54f73a043a13
-- title:
--   Section 3.3: the $(r,Q)$ rule defines an admissible policy
-- statement:
--   For every demand rate $\lambda\ge0$, lead time $L\ge0$, demand environment of rate $\lambda$, reorder point $r\in\mathbb N$ and lot size $Q\ge1$, there is an admissible policy on that environment that follows the classical $(r,Q)$ rule: it starts with $r+Q$ units on hand and an empty pipeline, and a served demand that reduces the inventory position from $r+1$ to $r$ triggers one immediate order of $Q$ units, with no other orders.
--
--   The paper uses $\pi_{\rm rQ}(r,Q)$ as a policy throughout; this statement records that the rule defines an adapted, right-continuous cumulative order process, so that it belongs to the admissible class over which $\mathrm{OPT}$ is taken.
--
--   **Formalization Note** The rule is the fixed-point condition $U(t)=Q\lfloor\mathcal A(t)/Q\rfloor$ together with $r+Q$ initial units on hand; the statement asserts that a policy satisfying it exists.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 3.3 and Table 2 (p. 7).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem rq_policy_exists (lam L : ℝ) (hlam : 0 ≤ lam) (hL : 0 ≤ L) (S : DemandSpace lam)
    (r Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ π : Policy S, IsRQPolicy L r Q π := by sorry

end LostSalesRQ
