-- Prove2me | Theorems.Thm_LefebvreVariations_stable_matching_four_at_least_ten
-- name    : LefebvreVariations.stable_matching_four_at_least_ten
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:19:50.719096+00:00
-- url     : https://prove2.me/theorems/c65ca1e2-ae28-43d2-8069-655231fc0670
-- title:
--   Lefebvre's variations, No. 254 — on a theme by Knuth: four men and four women can have an instance with at least ten stable matchings
-- statement:
--   Let four men and four women each rank all members of the other side (strict rankings, lower rank = preferred). A matching is a bijection $\sigma$ from men to women; a pair $(m,w)$ with $w\neq\sigma(m)$ blocks $\sigma$ if $m$ ranks $w$ above $\sigma(m)$ and $w$ ranks $m$ above $\sigma^{-1}(w)$. There exist rankings such that
--   $$\#\{\sigma\in S_4:\ \sigma\text{ has no blocking pair}\}\ \ge\ 10 .$$
--
--   The maximum number of stable matchings of an instance of size $n$ is a classical quantity; it is $1,2,3,10$ for $n=1,\dots,4$ (values due to Knuth, quoted from memory), so the value $10$ at $n=4$ already exceeds $2^{n-1}=8$. Lower-bound constructions for large $n$ are exponential, and sharp upper bounds are the subject of open problems on this topic.
--
--   **Formalization Note** The rankings are \texttt{mp, wp : Fin 4 $\to$ Equiv.Perm (Fin 4)}, with \texttt{mp m w} the rank of woman $w$ for man $m$ and \texttt{wp w m} the rank of man $m$ for woman $w$. Stable matchings are counted as the \texttt{Set.ncard} of the set of bijections with no blocking pair; the statement is an existence claim, not the exact maximum.
--
--   **Why this is a variation.** Variation on the open platform problem StableCountSub3.theorem_1_1 (fewer than 2.999^n stable matchings): a lower-bound witness for the maximum number of stable matchings at n = 4, showing the maximum is 10 > 2^3. An explicit instance exists, so the statement is true by a finite check. No formal link to the parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. E. Knuth, "Mariages stables et leurs relations avec d'autres problemes combinatoires" (Presses de l'Universite de Montreal, 1976): the maximum for n = 4 is 10 (cited from memory); exponential lower bounds: Irving and Leather, SIAM J. Comput. 15 (1986) (cited from memory). An explicit instance with exactly 10 stable matchings was found and verified here by exhaustive count over the 24 matchings (men's ranks [[2,0,3,1],[3,1,2,0],[0,2,1,3],[1,3,0,2]], women's ranks [[1,0,3,2],[3,2,1,0],[0,1,2,3],[2,3,0,1]]).

import Mathlib

namespace LefebvreVariations

/-- With four men and four women there is a stable marriage instance with at least ten stable
matchings. `mp m` is man `m`'s ranking of the women (a bijection onto `Fin 4`, lower rank =
preferred), `wp w` is woman `w`'s ranking of the men, and a matching is a bijection `σ`. A pair
`(m, w)` blocks `σ` if both prefer each other to their partners. Source: Knuth, *Mariages stables*
(1976), who shows that ten is the maximum for n = 4 (cited from memory); Irving–Leather 1986 for the
exponential constructions. -/
theorem stable_matching_four_at_least_ten :
    ∃ mp wp : Fin 4 → Equiv.Perm (Fin 4),
      10 ≤ {σ : Equiv.Perm (Fin 4) | ∀ m w, w ≠ σ m →
        ¬ (mp m w < mp m (σ m) ∧ wp w m < wp w (σ.symm w))}.ncard := by
  sorry

end LefebvreVariations
