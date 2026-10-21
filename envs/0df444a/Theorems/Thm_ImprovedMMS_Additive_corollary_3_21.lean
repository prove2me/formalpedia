-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_corollary_3_21
-- name    : ImprovedMMS.Additive.corollary_3_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:01.424111+00:00
-- url     : https://prove2.me/theorems/cc9d4719-5964-4032-baef-0ad3acfa16cf
-- title:
--   Corollary 3.21 (restated), p. 23 — each agent values at most one light good at ≥ 3/8
-- statement:
--   Let the agents of an instance $(\mathcal N,\mathcal M)$ have additive non-negative valuations with $\mathsf{MMS}_i=1$ for every $a_i\in\mathcal N$, and suppose the instance is $3/4$-irreducible. Let $L\subseteq\mathcal M$ be a set of goods each of which is worth less than $1/2$ to every agent of $\mathcal N$. Then for every agent $a_i\in\mathcal N$,
--   $$\big|\{\,b_j\in L:\ V_i(\{b_j\})\ge 3/8\,\}\big|\ \le\ 1.$$
--
--   It is the corollary of Lemma 3.20 used to pair light goods in cluster $\mathcal C_2$.
--
--   **Formalization Note** As for Lemma 3.20, the page's set $\mathcal X'\setminus\mathcal X'_{1/2}$, built by the algorithm, is replaced by an arbitrary set $L$ of goods each worth less than $1/2$ to every agent. $\mathsf{MMS}_i=1$ is the §3 standing assumption (p. 14).
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 23, Corollary 3.21 (restated; standing assumption MMS_i = 1, p. 14)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Corollary 3.21 (p. 23), restated, under the §3 normalization `MMS_i = 1` (p. 14): in a
3/4-irreducible instance, if every good of `L ⊆ M` is worth less than 1/2 to every agent, then
each agent values at most one good of `L` at 3/8 or more. -/
theorem corollary_3_21 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (hirr : IsIrreducible (3 / 4) v N M)
    (L : Finset (Fin m)) (hLM : L ⊆ M) (hL : ∀ b ∈ L, ∀ k ∈ N, v k {b} < 1 / 2) :
    ∀ i ∈ N, (L.filter (fun b => (3 / 8 : ℝ) ≤ v i {b})).card ≤ 1 := by sorry

end ImprovedMMS.Additive
