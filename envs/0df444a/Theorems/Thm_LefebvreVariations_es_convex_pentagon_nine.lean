-- Prove2me | Theorems.Thm_LefebvreVariations_es_convex_pentagon_nine
-- name    : LefebvreVariations.es_convex_pentagon_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:50:34.041205+00:00
-- url     : https://prove2.me/theorems/de92e565-b8b3-437b-8ef1-cc5cf5dc187d
-- title:
--   Lefebvre's variations, No. 94 — on a theme by Erdős and Szekeres: nine points in general position contain a convex pentagon
-- statement:
--   Let $S\subset\mathbb{R}^2$ be a set of $9$ points, no three collinear. Then $S$ contains $5$ points in convex position.
--
--   This is the case $n=5$ of the Erdős–Szekeres happy-ending conjecture, which asserts that $2^{n-2}+1$ points in general position always contain $n$ points in convex position. For $n=5$ the number $9=2^{3}+1$ is sharp. The conjecture is known for $n\le 6$ and open for $n\ge 7$, where only the Suk bound $2^{n+o(n)}$ is known.
--
--   **Formalization Note** `S : Finset (EuclideanSpace ℝ (Fin 2))` with `S.card = 9`. General position is the hypothesis that for pairwise distinct `a b c ∈ S` the set `{a, b, c}` is not collinear. The conclusion gives `T ⊆ S` with `T.card = 5` such that the inclusion `T → EuclideanSpace ℝ (Fin 2)` is `ConvexIndependent ℝ`, i.e. no point of `T` lies in the convex hull of the other four.
--
--   **Why this is a variation.** Small case of the Erdos-Szekeres happy-ending conjecture (ES(n) = 2^(n-2) + 1), namely n = 5, upper half ES(5) <= 9. The platform entry erdos_szekeres_conjecture is marked Disproved as formalized there, so there is no open platform parent; this statement is a faithful finite case of the mathematical conjecture, which is open for n >= 7.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the Erdos-Szekeres happy-ending conjecture; case n = 5, upper half ES(5) <= 9. The platform entry erdos_szekeres_conjecture is marked Disproved (as formalized), so it is not an open parent.
--   Verified by search: Erdos and Szekeres, Compositio Math. 2 (1935), 463-470, credit E. Makai with ES(5) = 9; the first complete published proof is by Kalbfleisch, Kalbfleisch and Stanton (1970) (title, venue and pages cited from memory: 'A combinatorial problem on convex n-gons', Proc. Louisiana Conf. Combinatorics, Graph Theory and Computing, 180-188). ES(6) = 17 by Szekeres and Peters (2006, computer search; ANZIAM J. 48, verified). The Suk bound 2^(n+o(n)) (J. Amer. Math. Soc. 30 (2017)) is cited from memory.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- ES(5) ≤ 9: among any nine points of the plane, no three collinear, some five are in convex
position. -/
theorem es_convex_pentagon_nine (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcard : S.card = 9)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ T ⊆ S, T.card = 5 ∧
      ConvexIndependent ℝ ((↑) : (↑T : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2)) := by
  sorry

end LefebvreVariations
