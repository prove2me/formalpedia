-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_claimB1_card_antitone
-- name    : MultiStoreAssort.SQR.claimB1_card_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:21.257539+00:00
-- url     : https://prove2.me/theorems/8ef645ec-4b20-4877-9ae2-c2df5a471422
-- title:
--   Claim in the proof of Lemma B.1, PDF p. 38 — the unique optimum of (B.1) has weakly fewer products for a larger βᵢ
-- statement:
--   Let $r_1>\dots>r_n>0$, $v_k>0$ and fix an assortment $S_2$. For a discount factor $\beta$ consider problem (B.1), which is problem (8):
--   $$
--   \max_{S\subseteq S_2}\ R_\beta(S)=\frac{W(S)}{1+V(S)}+\frac{\beta W(S_2\setminus S)}{\big(1+V(S)\big)\big(1+V(S)+\beta V(S_2\setminus S)\big)}.
--   $$
--   Let $0\le\beta''\le\beta'<1$. Suppose $S'\subseteq S_2$ is the unique optimal solution of the problem for $\beta=\beta'$ and $S''\subseteq S_2$ is the unique optimal solution for $\beta=\beta''$. Then
--   $$
--   |S'|\le|S''|.
--   $$
--   That is, when the optimal solution of (B.1) is unique, its size is weakly decreasing in $\beta$.
--
--   In the proof of Lemma B.1 this monotonicity, applied to $\beta_i=e^{-c_i}$ with $c_1\le\dots\le c_m$, yields the nested structure $S_1^*\subseteq\dots\subseteq S_{m-1}^*$.
--
--   **Formalization Note.** Uniqueness is stated explicitly: every other subset of $S_2$ has strictly smaller objective. The value $\beta''=0$ is allowed, as in the paper's proof.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 37–38, Appendix B.4, proof of Lemma B.1, problem (B.1) and Claim

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem claimB1_card_antitone {n : ℕ} (r v : Fin n → ℝ) (S2 S' S'' : Finset (Fin n)) (β' β'' : ℝ)
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hβ'' : 0 ≤ β'') (hββ : β'' ≤ β') (hβ' : β' < 1)
    (hS' : S' ⊆ S2) (huniq' : ∀ T : Finset (Fin n), T ⊆ S2 → T ≠ S' → rev8 r v β' S2 T < rev8 r v β' S2 S')
    (hS'' : S'' ⊆ S2)
    (huniq'' : ∀ T : Finset (Fin n), T ⊆ S2 → T ≠ S'' → rev8 r v β'' S2 T < rev8 r v β'' S2 S'') :
    S'.card ≤ S''.card := by sorry

end MultiStoreAssort.SQR
