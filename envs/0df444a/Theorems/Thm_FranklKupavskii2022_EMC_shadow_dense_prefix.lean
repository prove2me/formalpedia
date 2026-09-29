-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_shadow_dense_prefix
-- name    : FranklKupavskii2022.EMC.shadow_dense_prefix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:18:00.886423+00:00
-- url     : https://prove2.me/theorems/a275eae4-2706-40b5-811a-cd27f178912b
-- title:
--   Corollary 7: if $\nu(\partial\mathcal G)\le s$ then every member satisfies (13)
-- statement:
--   Let $k\ge2$ and $s\ge1$. For every initial $\mathcal G\subseteq\binom{[m]}{k}$ such that $\nu(\partial\mathcal G)\le s$ and every $F\in\mathcal G$ there is some $i$ with $1\le i<k$ such that
--
--   $$
--   |F\cap[i(s+1)-1]|\ge i+1. \tag{13}
--   $$
--
--   This makes the index $i_F$ (the largest such $i$) well defined and yields the decomposition $\mathcal G=\bigsqcup_{i=1}^{k-1}\mathcal G_i$.
--
--   **Formalization Note** The hypothesis $k\ge2$ is added: for $k=1$ the family $\{\{1\}\}$ is initial with $\nu(\partial\mathcal G)=\nu(\{\emptyset\})=1$, but no $i$ with $1\le i<1$ exists. The paper's proof applies (10) to $(k-1)$-sets, which uses $k-1\ge1$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Corollary 7, p. 4

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Corollary 7 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4): for every initial
`G ⊂ \binom{[m]}{k}` such that `ν(∂G) ≤ s` and every `F ∈ G` there exists some `i`, `1 ≤ i < k`,
such that `|F ∩ [i(s + 1) − 1]| ≥ i + 1` (13).

**Formalization Note.** `k ≥ 2` is added: at `k = 1`, `G = {{1}}` is initial with `∂G = {∅}` and
`ν(∂G) = 1 ≤ s`, but no `i` with `1 ≤ i < 1` exists; the paper's proof applies (10) to
`(k − 1)`-sets, i.e. uses `k − 1 ≥ 1`. `1 ≤ s` is the Sect. 1 standing assumption. -/
theorem shadow_dense_prefix (m k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k G)
    (hν : matchingNumber (∂ G) ≤ s) :
    ∀ F ∈ G, ∃ i, 1 ≤ i ∧ i < k ∧ i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by sorry

end FranklKupavskii2022.EMC
