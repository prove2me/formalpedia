-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_lemmaB2_revenue_ordered_within
-- name    : MultiStoreAssort.SQR.lemmaB2_revenue_ordered_within
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:19.418204+00:00
-- url     : https://prove2.me/theorems/d223bb35-9b8e-49a6-92f4-43108474ba26
-- title:
--   Lemma B.2, PDF p. 35 — problem (8) has an optimal S₁* that is revenue-ordered within the products of S₂
-- statement:
--   Let $r_1>\dots>r_n>0$, $v_k>0$, fix an assortment $S_2$ and a discount factor $\beta=e^{-c}$ with $0<\beta<1$. Write $V(S)=\sum_{k\in S}v_k$ and $W(S)=\sum_{k\in S}r_kv_k$, and consider problem (8):
--   $$
--   \max_{S_1\subseteq S_2}\ R(S_1)=\frac{W(S_1)}{1+V(S_1)}+\frac{\beta W(S_2\setminus S_1)}{\big(1+V(S_1)\big)\big(1+V(S_1)+\beta V(S_2\setminus S_1)\big)}.
--   $$
--   There exists an optimal solution $S_1^*$ that is revenue-ordered within the products of $S_2$: for some threshold, $S_1^*$ consists exactly of the products of $S_2$ with index below it (the empty set is allowed).
--
--   Problem (8) is the revenue of a store that first shows $S_1$ and then, to customers who bought nothing, the remaining products of $S_2$. The lemma is the key step towards revenue-ordered optimal assortments in every store.
--
--   **Formalization Note.** Products are 0-indexed, so "index below $j$" in Lean is the paper's "among the $j$ highest-revenue products"; positivity of the revenues is pinned (prices).
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 35, Lemma B.2; problem (8) on PDF p. 16; proof PDF pp. 38–39

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem lemmaB2_revenue_ordered_within {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (S2 : Finset (Fin n))
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ S1 : Finset (Fin n), S1 ⊆ S2 ∧ IsRevOrderedWithin S2 S1 ∧
      ∀ T : Finset (Fin n), T ⊆ S2 → rev8 r v β S2 T ≤ rev8 r v β S2 S1 := by sorry

end MultiStoreAssort.SQR
