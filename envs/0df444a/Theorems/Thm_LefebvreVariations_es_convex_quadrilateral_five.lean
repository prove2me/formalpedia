-- Prove2me | Theorems.Thm_LefebvreVariations_es_convex_quadrilateral_five
-- name    : LefebvreVariations.es_convex_quadrilateral_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:50:18.587268+00:00
-- url     : https://prove2.me/theorems/3f769d36-7fc9-4452-8ca8-a9536564dfa4
-- title:
--   Lefebvre's variations, No. 105 — on a theme by Erdős and Szekeres: five points in general position contain a convex quadrilateral
-- statement:
--   Let $S\subset\mathbb{R}^2$ be a set of $5$ points, no three collinear. Then $S$ contains $4$ points in convex position, that is, $4$ points none of which lies in the convex hull of the other three.
--
--   This is Esther Klein's observation that launched the Erdős–Szekeres happy-ending problem. The Erdős–Szekeres conjecture asserts that $2^{n-2}+1$ points in general position always contain $n$ points in convex position; this is the case $n=4$, where the value $5=2^{2}+1$ is sharp.
--
--   **Formalization Note** `S : Finset (EuclideanSpace ℝ (Fin 2))` with `S.card = 5`. General position is the hypothesis that for pairwise distinct `a b c ∈ S` the set `{a, b, c}` is not collinear. The conclusion gives `T ⊆ S` with `T.card = 4` such that the inclusion `T → EuclideanSpace ℝ (Fin 2)` is `ConvexIndependent ℝ`, i.e. no point of `T` lies in the convex hull of the others.
--
--   **Why this is a variation.** Small case of the Erdos-Szekeres happy-ending conjecture (ES(n) = 2^(n-2) + 1), namely n = 4: Klein's five-point lemma. The platform entry erdos_szekeres_conjecture is marked Disproved as formalized there, so there is no open platform parent; this statement is a faithful finite case of the mathematical conjecture, which is open for n >= 7.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the Erdos-Szekeres happy-ending conjecture; case n = 4. The platform entry erdos_szekeres_conjecture is marked Disproved (as formalized), so it is not an open parent.
--   The five-point case is Esther Klein's observation, reported in P. Erdos and G. Szekeres, 'A combinatorial problem in geometry', Compositio Math. 2 (1935), 463-470 (title, journal, year and pages verified by search; that the paper credits Klein for n = 4 is standard history, page-level attribution not re-checked).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Esther Klein's happy-ending lemma: among any five points of the plane, no three collinear,
some four are in convex position. -/
theorem es_convex_quadrilateral_five (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcard : S.card = 5)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ T ⊆ S, T.card = 4 ∧
      ConvexIndependent ℝ ((↑) : (↑T : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2)) := by
  sorry

end LefebvreVariations
