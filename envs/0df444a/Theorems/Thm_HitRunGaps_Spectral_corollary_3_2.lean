-- Prove2me | Theorems.Thm_HitRunGaps_Spectral_corollary_3_2
-- name    : HitRunGaps.Spectral.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:42.221576+00:00
-- url     : https://prove2.me/theorems/c20a9c68-0bd3-41fb-aab4-b85a69ed0fd6
-- title:
--   Corollary 3.2 — Improved Poincaré versus ordinary Poincaré and inradius
-- statement:
--   There is a universal $C>0$ such that every positive-dimensional convex body $K$, with actual maximum inscribed radius $r$, satisfies
--
--   $$C_{IPI}(\pi)\le C\frac{n^2C_{PI}(\pi)}{r^2}.$$
--
--   The inradius is positive and is computed from $K$, not supplied as an unrelated scalar. All positive radii and all source convex bodies are retained. This is the estimate needed to derive both dimension factors in the goal.
--
--   Differences from the source:
--   - encoding: real finite norms and constants on their natural domain → L² equivalence classes, Lebesgue normalization and extended nonnegative variational constants; reason: A.e. equality is intrinsic to L²; uniform normalization cancels in all ratios, and infeasible infima retain +∞
--   - encoding: the maximum inscribed radius r of a convex body → the supremum of radii of contained open balls, asserted positive; constants use interior K; reason: Bounded full-dimensional convex bodies have a finite positive maximal radius; the supremum agrees with the maximum and is unchanged by taking the interior
--   - generalization: a convex body K (compact convex set with nonempty interior) → any measurable bounded convex set with nonempty interior (open, closed or in between); reason: every compact convex body is such a set, so the statement specializes to the source's; the paper itself applies this result to the open K of Theorem 1.1, and all integrals, δ, the inradius and the constants (taken on interior K) agree for sets between the interior and the closure
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, PDF/printed p.9, Corollary 3.2

import Definitions.Def_HitRunGaps_Spectral_Samplers

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

theorem corollary_3_2 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∀ K : Set (Space n), IsConvexBody K →
    0 < inradius K ∧
    improvedPoincare (interior K) ≤ ENNReal.ofReal C * (n : ENNReal) ^ 2 *
      poincare (interior K) / ENNReal.ofReal ((inradius K) ^ 2) := by sorry

end HitRunGaps.Spectral
