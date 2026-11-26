-- Prove2me | Theorems.Thm_LefebvreVariations_es_no_convex_pentagon_eight
-- name    : LefebvreVariations.es_no_convex_pentagon_eight
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:50:55.57292+00:00
-- url     : https://prove2.me/theorems/4fdfc197-88e3-4acd-ba75-3e51f58aa1fc
-- title:
--   Lefebvre's variations, No. 92 — on a theme by Erdős and Szekeres: eight points in general position without a convex pentagon
-- statement:
--   There is a set $S\subset\mathbb{R}^2$ of $8$ points, no three collinear, containing no $5$ points in convex position.
--
--   This is the lower half of the exact value $ES(5)=9$ in the Erdős–Szekeres happy-ending problem: $8=2^{3}$ points in general position do not always contain a convex pentagon. The general construction, for every $n$, of $2^{n-2}$ points in general position with no convex $n$-gon is due to Erdős and Szekeres; whether $2^{n-2}+1$ points always suffice is open for $n\ge 7$.
--
--   **Formalization Note** The statement is an existence claim: `∃ S : Finset (EuclideanSpace ℝ (Fin 2))` with `S.card = 8`, such that for pairwise distinct `a b c ∈ S` the set `{a, b, c}` is not collinear, and every `T ⊆ S` with `T.card = 5` fails `ConvexIndependent ℝ` for the inclusion `T → EuclideanSpace ℝ (Fin 2)`.
--
--   **Why this is a variation.** Small case of the Erdos-Szekeres happy-ending conjecture (ES(n) = 2^(n-2) + 1), namely n = 5, sharpness half ES(5) > 8 (an explicit eight-point set). The platform entry erdos_szekeres_conjecture is marked Disproved as formalized there, so there is no open platform parent; this statement is a faithful finite case of the mathematical conjecture, which is open for n >= 7.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the Erdos-Szekeres happy-ending conjecture; case n = 5, lower half ES(5) > 8. The platform entry erdos_szekeres_conjecture is marked Disproved (as formalized), so it is not an open parent.
--   Verified in python (exact integer arithmetic): the points (8,4),(7,9),(10,4),(0,5),(2,6),(11,0),(8,3),(9,12) are distinct, have no three collinear and contain no five in convex position (all 56 five-subsets checked).
--   The general 2^(n-2) construction is due to Erdos and Szekeres, 'On some extremum problems in elementary geometry', Ann. Univ. Sci. Budapest. Eotvos Sect. Math. 3-4 (1960/61), 53-62 (cited from memory, not verified).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- ES(5) > 8: there are eight points of the plane, no three collinear, with no five in convex
position. -/
theorem es_no_convex_pentagon_eight :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = 8 ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
        ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∀ T ⊆ S, T.card = 5 →
        ¬ ConvexIndependent ℝ ((↑) : (↑T : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2)) := by
  sorry

end LefebvreVariations
