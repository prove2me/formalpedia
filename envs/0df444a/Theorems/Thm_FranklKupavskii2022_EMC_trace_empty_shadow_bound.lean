-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_trace_empty_shadow_bound
-- name    : FranklKupavskii2022.EMC.trace_empty_shadow_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:17:06.18308+00:00
-- url     : https://prove2.me/theorems/d266ec70-8e30-48ee-a58f-1e7fb06d04b2
-- title:
--   Lemma 5: $s|\partial\mathcal F(\emptyset)|\ge|\mathcal F(\emptyset)|$
-- statement:
--   Let $n,k,s$ be positive integers with $n\ge k(s+1)$. If $\mathcal F\subseteq\binom{[n]}{k}$ is initial and $\nu(\mathcal F)\le s$, then
--
--   $$
--   s\,|\partial\mathcal F(\emptyset)|\ge|\mathcal F(\emptyset)|, \tag{11}
--   $$
--
--   where $\mathcal F(\emptyset)$ is the family of members of $\mathcal F$ disjoint from $[s+1]$ and $\partial$ is the shadow. The lemma is due to Frankl (2013) and is quoted without proof; in the main proof it gives $q'\le s$ for the ratio $q'=|\mathcal F(\emptyset)|/|\partial\mathcal F(\emptyset)|$.
--
--   **Formalization Note** The standing assumption of Sect. 1 (positive $n,k,s$ with $n\ge k(s+1)$) is included; at $k=0$, $\mathcal F=\{\emptyset\}$ would give $0\ge1$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Lemma 5, p. 4 (citing [15] Frankl 2013)

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Lemma 5 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4, citing Frankl 2013 [15]): if
`F ⊂ \binom{[n]}{k}` is initial and `ν(F) ≤ s`, then `s|∂F(∅)| ≥ |F(∅)|` (11).

**Formalization Note.** `F(∅) = trace s F ∅` (the members of `F` disjoint from `[s+1]`), and
`∂F(∅)` is its shadow. The Sect. 1 standing assumption (p. 1) "positive integers n, k, s satisfy
n ≥ k(s + 1)" is kept as `1 ≤ k`, `1 ≤ s`, `k * (s + 1) ≤ n`; at `k = 0`, `F = {∅}` would give
`0 ≥ 1`. -/
theorem trace_empty_shadow_bound (n k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) :
    (trace s F ∅).card ≤ s * (∂ (trace s F ∅)).card := by sorry

end FranklKupavskii2022.EMC
