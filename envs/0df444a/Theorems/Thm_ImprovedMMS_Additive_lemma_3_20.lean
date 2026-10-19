-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_20
-- name    : ImprovedMMS.Additive.lemma_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:58.640913+00:00
-- url     : https://prove2.me/theorems/0d58dcf9-7040-4404-8c36-877f289311cc
-- title:
--   Lemma 3.20 (restated), p. 23 — in a 3/4-irreducible instance two goods each worth < 1/2 to all are worth < 3/4
-- statement:
--   Let the agents of an instance $(\mathcal N,\mathcal M)$ have additive non-negative valuations with $\mathsf{MMS}_i=1$ for every $a_i\in\mathcal N$, and suppose the instance is $3/4$-irreducible. Let $b_i\ne b_j$ be goods of $\mathcal M$ with $V_k(\{b_i\})<1/2$ and $V_k(\{b_j\})<1/2$ for every agent $a_k\in\mathcal N$. Then
--   $$V_k(\{b_i,b_j\})<3/4\qquad\text{for every } a_k\in\mathcal N.$$
--
--   It bounds the value of a merged vertex in the construction of cluster $\mathcal C_2$.
--
--   **Formalization Note** The page states the lemma for vertices $x_i,x_j\in\mathcal X'\setminus\mathcal X'_{1/2}$, a set built by the algorithm of §3.3. The algorithm is not formalized; membership is replaced by the property its proof uses (p. 56: one of $V_{k'}(\{b_i\})\ge 1/2$, $V_{k'}(\{b_j\})\ge 1/2$ "is contradiction, since we know both $x_i$ and $x_j$ belong to $\mathcal X'\setminus\mathcal X'_{1/2}$"): each of the two goods is worth less than $1/2$ to every agent. $\mathsf{MMS}_i=1$ is the §3 standing assumption (p. 14).
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 23, Lemma 3.20 (restated; proof p. 56; standing assumption MMS_i = 1, p. 14)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Lemma 3.20 (p. 23), restated, under the §3 normalization `MMS_i = 1` (p. 14): in a
3/4-irreducible instance, two distinct goods each worth less than 1/2 to every agent are together
worth less than 3/4 to every agent. -/
theorem lemma_3_20 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (hirr : IsIrreducible (3 / 4) v N M)
    (bi bj : Fin m) (hbi : bi ∈ M) (hbj : bj ∈ M) (hne : bi ≠ bj)
    (hbi_half : ∀ k ∈ N, v k {bi} < 1 / 2) (hbj_half : ∀ k ∈ N, v k {bj} < 1 / 2) :
    ∀ k ∈ N, v k {bi, bj} < 3 / 4 := by sorry

end ImprovedMMS.Additive
