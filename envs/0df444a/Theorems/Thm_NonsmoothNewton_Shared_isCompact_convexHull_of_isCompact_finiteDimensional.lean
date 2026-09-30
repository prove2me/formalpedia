-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_isCompact_convexHull_of_isCompact_finiteDimensional
-- name    : NonsmoothNewton.Shared.isCompact_convexHull_of_isCompact_finiteDimensional
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:46:28.995539+00:00
-- url     : https://prove2.me/theorems/723260f2-498b-4ab5-ad8f-0541f06df313
-- title:
--   The convex hull of a compact set is compact in finite dimension
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $s \subseteq E$ a compact set. Then the convex hull of $s$ is compact.
--
--   The result is false in general infinite-dimensional spaces, and it is the compactness input that the nonsmooth Newton argument needs for Clarke's generalized Jacobian, which is a convex hull of B-limit sets.
--
--   **Formalization Note** Put $D = \operatorname{finrank} \mathbb{R} E + 1$. Caratheodory's theorem in the form `eq_pos_convex_span_of_mem_convexHull` gives, for each point of the convex hull, a finite index type, points of $s$ that are affinely independent, and strictly positive weights summing to one whose weighted sum is the given point. Affine independence bounds the size: `AffineIndependent.card_le_finrank_succ` together with `Submodule.finrank_le` bounds the number of points by $D$.
--
--   All representations of all sizes are then packaged into one compact parameter space indexed by the finite type $\mathrm{Fin}(D+1)$, whose fibre over $m$ is a standard simplex over $\mathrm{Fin}(m)$ times a function space into $s$. The barycentre map is continuous by `continuous_sigma`, and its range is the convex hull, so the convex hull is a continuous image of a compact space.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), Section 3, p. 354. Compactness of the B-limit set and of Clarke's generalized Jacobian at a point, via the finite-dimensional fact that the convex hull of a compact set is compact; the compactness input for the uniform local inverse-norm bound required by NonsmoothNewton.Local.prop_3_1.

import Mathlib
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- In a finite-dimensional real normed space, the convex hull of a compact set
is compact.

Write `D = finrank ℝ E + 1`. By Caratheodory every point of the convex hull is
the barycentre of a weighted family of at most `D` points of the set, with
weights in a standard simplex. All such representations are packaged into a
single compact parameter space whose index type is finite and whose every fibre
is a product of compact spaces. The barycentre map is continuous on each fibre,
so `continuous_sigma` makes it continuous, and its range is exactly the convex
hull. The range of a continuous map from a compact space is compact.

The case `s = ∅` is covered without any extra hypothesis. -/
theorem isCompact_convexHull_of_isCompact_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by sorry

end NonsmoothNewton.Shared
