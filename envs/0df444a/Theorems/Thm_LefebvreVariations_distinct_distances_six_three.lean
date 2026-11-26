-- Prove2me | Theorems.Thm_LefebvreVariations_distinct_distances_six_three
-- name    : LefebvreVariations.distinct_distances_six_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:53:29.16131+00:00
-- url     : https://prove2.me/theorems/86c899fd-3f8b-5e09-b9de-76c09f34e0cc
-- title:
--   Lefebvre's variations, No. 75 — on a theme by Erdős: six points of the plane determine three distances
-- statement:
--   Any set of $6$ points in $\mathbb{R}^2$ determines at least $3$ distinct distances.
--
--   Let $g(n)$ be the minimum number of distinct distances determined by $n$ points of the plane. Erdős conjectured $g(n)\ge c\,n/\sqrt{\log n}$, and Guth–Katz proved $g(n)\gg n/\log n$. Here a planar set determining only two distinct distances has at most $5$ points (the regular pentagon is the extremal example), so $g(6)\ge3$.
--
--   **Formalization Note** `S : Finset (EuclideanSpace ℝ (Fin 2))` with `S.card = 6`. The number of distinct distances is the cardinality of the image of `S.offDiag` under `(p, q) ↦ dist p q`, so only distances between distinct points are counted. The conclusion is `3 ≤` that cardinality.
--
--   **Why this is a variation.** Small case of Erdos' distinct distances problem (minimum number of distinct distances among n planar points; order of magnitude n/sqrt(log n) conjectured, n/log n proved by Guth and Katz). The platform has the related open entry Esgk.general_position_distinct_distances_superlinear (general-position version), which this statement does not duplicate or imply; this is the small value g(6) >= 3.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Erdos' distinct distances problem; the platform has the related open entry Esgk.general_position_distinct_distances_superlinear (general-position version), not duplicated here. This is the small value g(6) >= 3 (a planar two-distance set has at most 5 points; the regular pentagon attains 5).
--   The bound of 5 for two-distance sets is classical and is not attributed to a named author here (a Kelly 1947 attribution could not be verified); see Erdos and Fishburn, Discrete Math. 160 (1996), 115-125 (verified by search). Guth and Katz, Ann. of Math. 181 (2015), 155-190 (cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Any six points of the plane determine at least three distinct distances (a planar set with
only two distinct distances has at most five points). -/
theorem distinct_distances_six_three (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcard : S.card = 6) :
    3 ≤ (S.offDiag.image (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist p.1 p.2)).card := by
  sorry

end LefebvreVariations
