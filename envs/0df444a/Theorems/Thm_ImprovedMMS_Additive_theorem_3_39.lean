-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_theorem_3_39
-- name    : ImprovedMMS.Additive.theorem_3_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:09.697537+00:00
-- url     : https://prove2.me/theorems/f9fe045f-8550-4e2b-a308-dd3ee78782b1
-- title:
--   Theorem 3.39 (existence form, p. 5, Table 1), p. 30 — every instance with additive agents admits a 3/4-MMS allocation
-- statement:
--   Let $n\ge 1$ agents $a_1,\dots,a_n$ have additive valuations $V_i$ over a finite set $\mathcal M$ of $m$ goods: $V_i(S)=\sum_{b\in S}V_i(\{b\})$ and $V_i(S)\ge 0$ for every $S\subseteq\mathcal M$. Let
--   $$\mathsf{MMS}_i=\max_{(P_1,\dots,P_n)}\ \min_{1\le j\le n}V_i(P_j)$$
--   be the maxmin share of $a_i$, the maximum over all partitions of $\mathcal M$ into $n$ disjoint parts. Then there is an allocation $\langle A_1,\dots,A_n\rangle$, a partition of $\mathcal M$ among the agents, with
--   $$V_i(A_i)\ \ge\ \tfrac34\,\mathsf{MMS}_i\qquad\text{for every agent } a_i.$$
--
--   This is the paper's main result for additive agents; it improves the factor $2/3$ of Procaccia and Wang.
--
--   **Formalization Note** The sentence printed as Theorem 3.39 on p. 30 ("All the agents are satisfied before the termination of the algorithm") is about the paper's algorithm; Table 1 (p. 5) attributes to Theorem 3.39 the existential result stated here, which is also the first sentence of the restated Theorem 3.40 on p. 5. The algorithm is not formalized. No normalisation $\mathsf{MMS}_i=1$ and no irreducibility is assumed (both are proof devices of §3). An allocation is a map `A : Fin m → Fin n`, so every good goes to exactly one agent; $\mathsf{MMS}_i$ is `mms (v i) n univ` over labelled, possibly empty parts. The hypothesis $n\ge 1$ is necessary: with no agents and at least one good no allocation exists. Additivity is the published `IsAdditive` (sum of singleton values, non-negative); the paper's printed formula on p. 12 has a sign slip ($V(S_1)+V(S_2)=V(S_1\cup S_2)-V(S_1\cap S_2)$) and the paper uses only the sum form.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 30, Theorem 3.39 (existence form as restated on p. 5 and in Table 1)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Theorem 3.39 in its existence form (p. 5, Table 1; p. 30): every instance with `n ≥ 1`
additive agents admits a 3/4-MMS allocation of all `m` goods, `V_i(A_i) ≥ 3/4 · MMS_i` with
`MMS_i = MMS^n_{V_i}(M)`. -/
theorem theorem_3_39 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : IsAdditive v) :
    ∃ A : Fin m → Fin n, ∀ i : Fin n,
      (3 / 4 : ℝ) * mms (v i) n Finset.univ ≤ v i (Finset.univ.filter (fun b => A b = i)) := by sorry

end ImprovedMMS.Additive
