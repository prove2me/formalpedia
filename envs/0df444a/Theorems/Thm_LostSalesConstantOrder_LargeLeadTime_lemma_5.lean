-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_5
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:45.388441+00:00
-- url     : https://prove2.me/theorems/f4de798b-067c-476e-ae64-d13655c52c05
-- title:
--   Lemma 5: an optimal policy for problem (1) never orders more than Q
-- statement:
--   In the lost-sales system with lead time $L$, costs $h,c>0$ and demand law $\mathcal D$ (finite third moment, not deterministic), let $T>L$. Problem (1), $\inf_\pi\sum_{t=L+1}^{T+L}\mathbb E[C^\pi_t]$, has an optimal policy $\bar\pi$ that with probability one never orders more than $Q$, the $c/(c+h)$ quantile of $\mathcal D$:
--   $$
--   \exists\,\bar\pi:\quad \sum_{t=L+1}^{T+L}\mathbb E[C^{\bar\pi}_t]=\mathrm{OPT}(L,T)\quad\text{and}\quad\mathbb P(\bar\pi\text{ orders at most }Q\text{ in every period})=1.
--   $$
--   In the paper's words, $\mathbf x^{\bar\pi}_t\le Q\mathbf 1$ for all $t\in[L+1,T]$. The result is due to Zipkin (2008), *On the structure of lost-sales inventory models*, Operations Research 56(4), whose discounted dynamic program shows that optimal order-up-to bounds are capped by the myopic newsvendor level.
--
--   It provides the bounded optimal policy $\bar\pi$ whose cost Lemmas 6–7, Theorem 8 and Corollary 12 bound from below.
--
--   **Formalization Note** The optimum is over the model's history-dependent randomized admissible policies, a class containing the paper's class $\Pi$; existence of an optimal policy (asserted implicitly by the paper's Lemma 5, see the Remark on p. 8) is stated for this class. "Never orders more than $Q$" is stated for the order in every period, which implies the paper's pipeline form $\mathbf x_t\le Q\mathbf 1$; orders after period $T$ do not affect the objective.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 7, Lemma 5 (citing Zipkin 2008b), Remark p. 8

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 5, p. 7 ([47], Zipkin 2008b): problem (1) has an optimal policy which with
probability one never orders more than `Q`. The optimum is over the full admissible class of the
`CappedBaseStock` model (history-dependent, randomized), which contains the paper's class `Π`. -/
theorem lemma_5 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (T : ℕ) (hT : prm.L < T) :
    ∃ π : CappedBaseStock.AdmissiblePolicy,
      costLT P prm π T = optLT P prm T ∧ OrdersBounded P π (Qlevel P prm) := by sorry

end LostSalesConstantOrder.LargeLeadTime
