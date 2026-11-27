-- Prove2me | Theorems.Thm_LefebvreVariations_stable_matching_three_at_most_three
-- name    : LefebvreVariations.stable_matching_three_at_most_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:19:30.923239+00:00
-- url     : https://prove2.me/theorems/4fe3b835-b756-40cf-a4b4-c560ae0b7d70
-- title:
--   Lefebvre's variations, No. 253 — on a theme by Knuth: with three men and three women a stable marriage instance has at most three stable matchings
-- statement:
--   Let three men and three women each rank all members of the other side (strict rankings, lower rank = preferred). A matching is a bijection $\sigma$ from men to women, and a pair $(m,w)$ with $w\neq\sigma(m)$ blocks $\sigma$ if $m$ ranks $w$ above $\sigma(m)$ and $w$ ranks $m$ above $\sigma^{-1}(w)$. For every such instance,
--   $$\#\{\sigma\in S_3:\ \sigma\text{ has no blocking pair}\}\ \le\ 3 .$$
--
--   The maximum number of stable matchings over all instances of size $n$ is a classical quantity of the stable marriage problem; it is $1,2,3,10$ for $n=1,\dots,4$ (values due to Knuth, quoted from memory), and upper bounds of the form $c^n$ are the subject of the open problems on this topic. The bound $3$ is attained at $n=3$; the statement checked here is the upper bound.
--
--   **Formalization Note** The rankings are \texttt{mp, wp : Fin 3 $\to$ Equiv.Perm (Fin 3)}, with \texttt{mp m w} the rank of woman $w$ for man $m$ and \texttt{wp w m} the rank of man $m$ for woman $w$. Stable matchings are counted as the \texttt{Set.ncard} of the set of bijections $\sigma$ with no blocking pair.
--
--   **Why this is a variation.** Variation on the open platform problem StableCountSub3.theorem_1_1 (fewer than 2.999^n stable matchings), which concerns upper bounds on the maximum number of stable matchings in an instance of size n. This statement is the exact maximum at n = 3, an upper bound proved by finite enumeration. No formal link to the parent is claimed: it is a small case of the same quantity, in its own self-contained definitions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. E. Knuth, "Mariages stables et leurs relations avec d'autres problemes combinatoires" (Presses de l'Universite de Montreal, 1976): maximum numbers of stable matchings for small n (values 1, 2, 3, 10 cited from memory). Stable matchings: Gale and Shapley, Amer. Math. Monthly 69 (1962). The bound for n = 3 was also checked here by exhaustive enumeration of all 46656 instances (maximum found: 3).

import Mathlib

namespace LefebvreVariations

/-- With three men and three women, no instance of the stable marriage problem has more than three
stable matchings (and three is attained). `mp m` is man `m`'s ranking of the women (a bijection
onto `Fin 3`, lower rank = preferred), `wp w` is woman `w`'s ranking of the men, and a matching is
a bijection `σ` (man `m` is matched to woman `σ m`). A pair `(m, w)` blocks `σ` if both prefer each
other to their partners. Source: stable matchings, Gale–Shapley 1962 and Knuth, *Mariages stables*
(1976); the exact maxima 1, 2, 3, 10 for n = 1..4 are cited from memory. -/
theorem stable_matching_three_at_most_three (mp wp : Fin 3 → Equiv.Perm (Fin 3)) :
    {σ : Equiv.Perm (Fin 3) | ∀ m w, w ≠ σ m →
        ¬ (mp m w < mp m (σ m) ∧ wp w m < wp w (σ.symm w))}.ncard ≤ 3 := by
  sorry

end LefebvreVariations
