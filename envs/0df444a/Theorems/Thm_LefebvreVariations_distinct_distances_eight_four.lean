-- Prove2me | Theorems.Thm_LefebvreVariations_distinct_distances_eight_four
-- name    : LefebvreVariations.distinct_distances_eight_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:53:12.790711+00:00
-- url     : https://prove2.me/theorems/bd0ab00f-2bd6-53e7-ab4b-ea00d47a6d56
-- title:
--   Lefebvre's variations, No. 114 — on a theme by Erdős: eight points of the plane determine four distances
-- statement:
--   Any set of $8$ points in $\mathbb{R}^2$ determines at least $4$ distinct distances.
--
--   Let $g(n)$ be the minimum number of distinct distances determined by $n$ points of the plane. Erdős conjectured $g(n)\ge c\,n/\sqrt{\log n}$, and Guth–Katz proved $g(n)\gg n/\log n$. The small values are known exactly: $g(n)=3$ for $n=6,7$ and $g(8)=4$, because a planar set determining only three distinct distances has at most $7$ points. This statement is the bound $g(8)\ge4$.
--
--   **Formalization Note** `S : Finset (EuclideanSpace ℝ (Fin 2))` with `S.card = 8`. The number of distinct distances is the cardinality of the image of `S.offDiag` under `(p, q) ↦ dist p q`, so only distances between distinct points are counted. The conclusion is `4 ≤` that cardinality.
--
--   **Why this is a variation.** Small case of Erdos' distinct distances problem (minimum number of distinct distances among n planar points; order of magnitude n/sqrt(log n) conjectured, n/log n proved by Guth and Katz). The platform has the related open entry Esgk.general_position_distinct_distances_superlinear (general-position version), which this statement does not duplicate or imply; this is the exact small value g(8) >= 4.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Erdos' distinct distances problem (minimum number of distinct distances determined by n planar points; conjectured order n/sqrt(log n), proved up to a logarithm by Guth and Katz); the platform has the related open entry Esgk.general_position_distinct_distances_superlinear (general-position version), not duplicated here. This is the exact small value g(8) >= 4.
--   Sources: P. Erdos and P. Fishburn, 'Maximum planar sets that determine k distances', Discrete Math. 160 (1996), 115-125 (verified by search: maximum sizes 5, 7, 9, 12 for k = 2, 3, 4, 5; the k = 5 case is attributed to Shinohara in one source, details cited from memory). A planar set with only three distances has at most 7 points, hence 8 points need at least 4. Guth and Katz, Ann. of Math. 181 (2015), 155-190 (cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Any eight points of the plane determine at least four distinct distances (a planar set with
only three distinct distances has at most seven points; Erdős–Fishburn). -/
theorem distinct_distances_eight_four (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcard : S.card = 8) :
    4 ≤ (S.offDiag.image (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist p.1 p.2)).card := by
  sorry

end LefebvreVariations
