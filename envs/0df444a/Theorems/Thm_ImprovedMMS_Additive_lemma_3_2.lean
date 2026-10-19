-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_2
-- name    : ImprovedMMS.Additive.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:36.14441+00:00
-- url     : https://prove2.me/theorems/8341682a-2f55-4eb8-80c3-cde4d0dbfe3d
-- title:
--   Lemma 3.2, p. 17 — in a 3/4-irreducible instance a pair worth ≥ 3/4 to one agent is worth > 1 to another
-- statement:
--   Let the agents of an instance $(\mathcal N,\mathcal M)$ have additive non-negative valuations with $\mathsf{MMS}_i=1$ for every $a_i\in\mathcal N$, and suppose the instance is $3/4$-irreducible. If $V_i(\{b_j,b_k\})\ge 3/4$ for an agent $a_i\in\mathcal N$ and goods $b_j,b_k\in\mathcal M$, then there is an agent $a_{i'}\in\mathcal N$, $a_{i'}\ne a_i$, with
--   $$V_{i'}(\{b_j,b_k\})>1.$$
--
--   It extends Lemma 3.1 from single goods to pairs and drives the pairing steps of the clustering phase.
--
--   **Formalization Note** $\mathsf{MMS}_i=1$ is the §3 standing assumption (p. 14), stated as a hypothesis.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 17, Lemma 3.2 (standing assumption MMS_i = 1, p. 14)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Lemma 3.2 (p. 17), under the §3 normalization `MMS_i = 1` (p. 14): in a 3/4-irreducible
instance, if `V_i({b_j, b_k}) ≥ 3/4` then some other agent `i'` has `V_{i'}({b_j, b_k}) > 1`. -/
theorem lemma_3_2 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (hirr : IsIrreducible (3 / 4) v N M)
    (i : Fin n) (hi : i ∈ N) (bj bk : Fin m) (hbj : bj ∈ M) (hbk : bk ∈ M)
    (h : (3 / 4 : ℝ) ≤ v i {bj, bk}) :
    ∃ i' ∈ N, i' ≠ i ∧ 1 < v i' {bj, bk} := by sorry

end ImprovedMMS.Additive
