-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_ineq_16
-- name    : ImprovedMMS.Additive.ineq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:39.247603+00:00
-- url     : https://prove2.me/theorems/b7893424-cc17-4d3c-81f0-78ccfb3cf6bb
-- title:
--   Proof of Lemma 3.2, inequality (16), p. 52 — removing a pair worth ≤ 1 keeps MMS^{n−1} ≥ 1
-- statement:
--   Let agent $a_{i'}$ have an additive non-negative valuation $V_{i'}$ on the goods $\mathcal M$ of an instance with $n=|\mathcal N|\ge 2$ agents, with $\mathsf{MMS}_{i'}=\mathsf{MMS}^n_{V_{i'}}(\mathcal M)=1$. If $b_j,b_k\in\mathcal M$ satisfy $V_{i'}(\{b_j,b_k\})\le 1$, then
--   $$\mathsf{MMS}^{\,n-1}_{V_{i'}}(\mathcal M\setminus\{b_j,b_k\})\ \ge\ 1.$$
--
--   Inequality (16) is the step of the proof of Lemma 3.2 that keeps every other agent's share after a pair of goods is given away; Lemma 3.3 applies it repeatedly.
--
--   **Formalization Note** The hypothesis $n\ge 2$ is the context of the page (agents $a_i$ and $a_{i'}\ne a_i$ both exist) and is needed: with $n=1$ the left side is a maxmin share over $0$ parts, which the formalization evaluates to $0$.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 52, Appendix B, proof of Lemma 3.2, inequality (16)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Inequality (16), proof of Lemma 3.2 (p. 52): if `MMS_{i'} = 1`, there are at least two agents
and `V_{i'}({b_j, b_k}) ≤ 1`, then `MMS^{n-1}_{i'}(M \ {b_j, b_k}) ≥ 1`. -/
theorem ineq_16 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hcard : 2 ≤ N.card)
    (i' : Fin n) (hi' : i' ∈ N) (h1 : mms (v i') N.card M = 1)
    (bj bk : Fin m) (hbj : bj ∈ M) (hbk : bk ∈ M) (hle : v i' {bj, bk} ≤ 1) :
    1 ≤ mms (v i') (N.card - 1) (M \ {bj, bk}) := by sorry

end ImprovedMMS.Additive
