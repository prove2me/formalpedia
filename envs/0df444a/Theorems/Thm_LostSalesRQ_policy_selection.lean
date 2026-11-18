-- Prove2me | Theorems.Thm_LostSalesRQ_policy_selection
-- name    : LostSalesRQ.policy_selection
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:33:45.08692+00:00
-- url     : https://prove2.me/theorems/8cbd25e3-aee8-408a-b4d7-b64fe171ef68
-- title:
--   Corollary 1: an explicit policy selection
-- statement:
--   Suppose $h,\lambda>0$ and $L,p,K\ge0$, and write $\mu=\lambda L$, $a=p\lambda/h$, $k=K\lambda/h$. Let $S^\star$ be any cost-minimizing integer base-stock level at zero setup cost, i.e. $L_{S^\star}(a)\le L_j(a)$ for all $j\in\mathbb N$, and set $Q_k=\max\{1,\lfloor\sqrt{2k}\rfloor\}$, $b_k=(Q_k-1)/2+k/Q_k$. If $S^\star\ge1$ and $U_\mu(a)+b_k<a$, choose the $(r,Q)=(S^\star-1,Q_k)$ policy; otherwise choose no replenishment. Then:
--
--   1. on every demand environment of rate $\lambda$, such a policy exists;
--   2. every selected policy $\pi$ satisfies
--   $$C(\pi)\le R\,\mathrm{OPT},\qquad R=\begin{cases}\sqrt2,&K=0,\\ (\sqrt2+\sqrt6)/2,&\text{in general};\end{cases}$$
--   3. when $K=0$, $\pi$ is an integer base-stock policy (including level zero) and is optimal among integer base-stock policies: $C(\pi)\le C(\pi')$ for every $\pi'\in\Pi_{\rm S}$.
--
--   The corollary turns the guarantee into a finite procedure that needs neither $\mathrm{OPT}$ nor any optimization over $Q$.
--
--   **Formalization Note** The selected policy is described by the predicate `IsSelectedPolicy`; its existence is part of the statement, so the conclusions are not vacuous. For $K=0$ the stated factor is $\sqrt2$; for $K>0$ it is $(\sqrt2+\sqrt6)/2$.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Corollary 1 (p. 9).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem policy_selection (lam L h p K : ℝ) (hlam : 0 < lam) (hL : 0 ≤ L) (hh : 0 < h)
    (hp : 0 ≤ p) (hK : 0 ≤ K) (S : DemandSpace lam) (Sstar : ℕ)
    (hS : ∀ j : ℕ, baseStockCost (lam * L) (p * lam / h) Sstar ≤
      baseStockCost (lam * L) (p * lam / h) j) :
    (∃ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) (K * lam / h) Sstar π) ∧
    ∀ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) (K * lam / h) Sstar π →
      π.avgCost L h p K ≤
          ENNReal.ofReal (if K = 0 then Real.sqrt 2 else (Real.sqrt 2 + Real.sqrt 6) / 2) *
            OPT lam L h p K ∧
        (K = 0 → π ∈ baseStockFamily S L ∧
          ∀ π' ∈ baseStockFamily S L, π.avgCost L h p 0 ≤ π'.avgCost L h p 0) := by sorry

end LostSalesRQ
