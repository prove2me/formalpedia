-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_3
-- name    : ImprovedMMS.Additive.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:07.353223+00:00
-- url     : https://prove2.me/theorems/5f49f4c3-faef-446b-a963-7b4c6ca0ceaa
-- title:
--   Lemma 3.3, p. 17 — in a 3/4-irreducible instance every family of disjoint satisfying pairs violates (i)–(iii)
-- statement:
--   Let the agents of an instance $(\mathcal N,\mathcal M)$ have additive non-negative valuations with $\mathsf{MMS}_i=1$ for every $a_i\in\mathcal N$, and suppose the instance is $3/4$-irreducible. Let $T=\{a_{i_1},\dots,a_{i_{|T|}}\}\subseteq\mathcal N$ be a non-empty set of agents, and assign to each $a_{i_a}\in T$ two goods $b_{j_{2a-1}},b_{j_{2a}}\in\mathcal M$; let $S$ be the set of all these goods. Then at least one of the following conditions is violated:
--
--   1. $|S|=2|T|$ (the $2|T|$ goods are distinct);
--   2. $V_{i_a}(\{b_{j_{2a-1}},b_{j_{2a}}\})\ge 3/4$ for every $a_{i_a}\in T$;
--   3. $V_i(\{b_{j_{2a-1}},b_{j_{2a}}\})\le 1$ for every $a_i\in\mathcal N\setminus T$ and every $1\le a\le|T|$.
--
--   Equivalently, if (i)–(iii) hold the instance is $3/4$-reducible. This is the many-pair version of Lemma 3.2.
--
--   **Formalization Note** The goods of agent $a\in T$ are `p a` and `q a`, and $S$ is `T.image p ∪ T.image q`. $T$ is required non-empty: for $T=\emptyset$ the three conditions hold vacuously and "one of them is violated" would be false. $\mathsf{MMS}_i=1$ is the §3 standing assumption (p. 14).
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 17, conditions (i)–(iii) and Lemma 3.3 (standing assumption MMS_i = 1, p. 14)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Lemma 3.3 (p. 17), under the §3 normalization `MMS_i = 1` (p. 14): in a 3/4-irreducible
instance, for every non-empty set `T ⊆ N` of agents and goods `b_{j_{2a-1}} = p a`,
`b_{j_{2a}} = q a` (`a ∈ T`) of `M`, at least one of the conditions fails:
(i) `|S| = 2|T|` for `S = {p a, q a : a ∈ T}`;
(ii) `V_a({p a, q a}) ≥ 3/4` for every `a ∈ T`;
(iii) `V_i({p a, q a}) ≤ 1` for every `i ∈ N \ T` and every `a ∈ T`. -/
theorem lemma_3_3 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (hirr : IsIrreducible (3 / 4) v N M)
    (T : Finset (Fin n)) (hTN : T ⊆ N) (hT : T.Nonempty)
    (p q : Fin n → Fin m) (hp : ∀ a ∈ T, p a ∈ M) (hq : ∀ a ∈ T, q a ∈ M) :
    ¬ ((T.image p ∪ T.image q).card = 2 * T.card ∧
        (∀ a ∈ T, (3 / 4 : ℝ) ≤ v a {p a, q a}) ∧
        (∀ i ∈ N \ T, ∀ a ∈ T, v i {p a, q a} ≤ 1)) := by sorry

end ImprovedMMS.Additive
