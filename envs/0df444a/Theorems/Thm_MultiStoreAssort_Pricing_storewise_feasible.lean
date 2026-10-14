-- Prove2me | Theorems.Thm_MultiStoreAssort_Pricing_storewise_feasible
-- name    : MultiStoreAssort.Pricing.storewise_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:58.282323+00:00
-- url     : https://prove2.me/theorems/43c34cf4-9595-459e-b3ee-1ebc143cca81
-- title:
--   App. E.1, PDF p. 47 — store i's SMR revenue is at most (14)'s objective at S = S̄ with prices pₖ = (αᵢₖ − log ṽᵢₖ)/βᵢₖ off Sᵢ
-- statement:
--   Consider the multistore joint pricing model under simultaneous recommendation, with $\alpha_{ik}>0$, $\beta_{ik}>0$, discounts $c^k_{ij}\ge 0$ and $c^k_{ii}=0$. Fix an assortment profile $\mathbf S$, real prices $\mathbf P=(p_{ik})$, a best-store rule $l$ for $(\mathbf S,\mathbf P)$, and a store $i$. Define a price vector for the single-store problem (14) with parameters $\alpha_k=\alpha_{ik}$, $\beta_k=\beta_{ik}$ by
--   $$p_k=\begin{cases}p_{ik}, & k\in S_i,\\[2pt] \dfrac{1}{\beta_{ik}}\bigl(\alpha_{ik}-\log\tilde v_{ik}(\mathbf S)\bigr), & k\notin S_i.\end{cases}$$
--   Then
--
--   1. $p_k\ge\tilde p_{ik}(\mathbf S)$ for every $k\in\bar S\setminus S_i$, and
--   2. store $i$'s expected revenue in (13) is at most the objective of (14) at the assortment $S=\bar S$ and the prices $(p_k)$:
--   $$\frac{\sum_{k\in S_i}p_{ik}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde p_{ik}(\mathbf S)\tilde v_{ik}(\mathbf S)}{1+\sum_{k\in S_i}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde v_{ik}(\mathbf S)}\ \le\ \frac{\sum_{k\in\bar S}p_k\exp(\alpha_{ik}-\beta_{ik}p_k)}{1+\sum_{k\in\bar S}\exp(\alpha_{ik}-\beta_{ik}p_k)}.$$
--
--   This is the first step of the proof of Theorem 6: the cross-store purchases are re-expressed as own-store purchases at a price at least as high.
--
--   **Formalization Note** The prices $p_k$ for $k\notin\bar S$ are irrelevant to (14) at $S=\bar S$; the Lean vector uses the second branch for every $k\notin S_i$. The hypotheses $\alpha_{ik}>0$ and $c^k_{ii}=0$ are the section's standing assumptions and are carried for uniformity.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), Online Supplement App. E.1, proof of Theorem 6, PDF p. 47

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

namespace MultiStoreAssort.Pricing
open Finset

theorem storewise_feasible {m n : ℕ} (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (hα : ∀ i k, 0 < α i k) (hβ : ∀ i k, 0 < β i k) (hc : ∀ i j k, 0 ≤ c i j k)
    (hcii : ∀ i k, c i i k = 0)
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m)
    (hl : IsBestStore α β c P S l) (i : Fin m) :
    (∀ k ∈ MultiStoreAssort.SMR.Sbar S \ S i,
        pTilde P l i k ≤ (α i k - Real.log (vTilde α β c P l i k)) / β i k) ∧
      storeRev13 α β c S P l i ≤
        rev14 (α i) (β i) (MultiStoreAssort.SMR.Sbar S)
          (fun k => if k ∈ S i then P i k else (α i k - Real.log (vTilde α β c P l i k)) / β i k) := by sorry

end MultiStoreAssort.Pricing
