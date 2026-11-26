-- Prove2me | Theorems.Thm_LefebvreVariations_emcMax_one
-- name    : LefebvreVariations.emcMax_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:24:16.224794+00:00
-- url     : https://prove2.me/theorems/198f632e-a76b-4fd8-aa5b-64355101a699
-- title:
--   Lefebvre's variations, No. 49 — on a theme by Erdős, Ko and Rado: the Erdős matching conjecture at s = 1 (Erdős–Ko–Rado)
-- statement:
--   This is the Erdős–Ko–Rado theorem in the formulation of the Erdős Matching Conjecture at $s=1$.
--
--   Let $n\ge2k\ge2$ and let $\mathcal F$ be a family of $k$-element subsets of $\{1,\dots,n\}$ with matching number at most $1$, that is, no two members of $\mathcal F$ are disjoint. Then the maximum size of such a family is
--
--   $$
--   \binom nk-\binom{n-1}k=\binom{n-1}{k-1},
--   $$
--
--   attained by the star of all $k$-sets containing a fixed element.
--
--   The Erdős Matching Conjecture asserts that for matching number at most $s$ and $n\ge(s+1)k$ the maximum is $\binom nk-\binom{n-s}k$ (the family of sets meeting a fixed $s$-set) or the clique alternative for smaller $n$; the case $s=1$ is the Erdős–Ko–Rado theorem, which ties the platform's formulation to the classical result.
--
--   **Formalization Note** The maximum is the mission's `emcMax n k s`, over families of $k$-subsets of $\{1,\dots,n\}$ with matching number at most $s$.
--
--   **Why this is a variation.** This varies the Erdős Matching Conjecture, which gives the maximum size of a family of $k$-subsets of $[n]$ with no $s+1$ pairwise disjoint members. It is the case $s=1$, the first size of the parent, which is exactly the Erdős–Ko–Rado theorem: the maximum is $\binom{n}{k}-\binom{n-1}{k}$. It anchors the parent's formula at its smallest parameter.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   P. Erdős, C. Ko and R. Rado, Intersection theorems for systems of finite sets, Quart. J. Math. Oxford Ser. (2) 12 (1961), 313–320; the conjecture: P. Erdős, A problem on independent r-tuples, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 8 (1965), 93–95. Parent problem: FranklKupavskii2022.EMC (Erdős matching conjecture).

import Definitions.Def_FranklKupavskii2022_EMC_emcMax

set_option autoImplicit false

namespace LefebvreVariations

open FranklKupavskii2022.EMC

/-- **The Erdős Matching Conjecture at `s = 1` is the Erdős–Ko–Rado theorem.** For `k ≥ 1` and
`n ≥ 2k`, `m(n,k,1) = C(n,k) − C(n−1,k)` (= `C(n−1,k−1)`): a family of `k`-subsets of `[n]` with no
two disjoint members has at most `C(n−1,k−1)` members, attained by the star (Erdős–Ko–Rado,
*Quart. J. Math. Oxford Ser. (2)* 12 (1961) 313–320, Thm 1; the conjecture for general `s` is
Erdős, *Ann. Univ. Sci. Budapest Eötvös Sect. Math.* 8 (1965) 93–95 — formula `m(n,k,s)=C(n,k)−C(n−s,k)` for
`n ≥ (s+1)k`; Frankl 2013, *J. Combin. Theory Ser. A* 120, 1068–1072 for `n ≥ (2s+1)k−s`). This is
the instance `s = 1` of the parent's formula, with the threshold `n ≥ 2k` of the paper's standing
assumption `n ≥ k(s+1)`. -/
theorem emcMax_one (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    emcMax n k 1 = n.choose k - (n - 1).choose k := by
  sorry

end LefebvreVariations
