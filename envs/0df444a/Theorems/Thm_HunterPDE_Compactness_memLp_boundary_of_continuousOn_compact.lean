-- Prove2me | Theorems.Thm_HunterPDE_Compactness_memLp_boundary_of_continuousOn_compact
-- name    : HunterPDE.Compactness.memLp_boundary_of_continuousOn_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T09:46:50.914862+00:00
-- url     : https://prove2.me/theorems/58e07c12-d5f0-43b2-bf74-4cab2c0f5876
-- title:
--   Boundary restriction of a continuous compact half-space function belongs to every Lp
-- statement:
--   Let $f$ be real valued and continuous on the closed upper half-space in dimension $m+1$. Suppose it vanishes there outside a compact subset of the ambient Euclidean space. Its restriction to the boundary, identified with $\mathbb R^m$, belongs to $L^p$ for every exponent $0\le p\le\infty$. The case $m=0$ is included. Only continuity on the closed half-space is required; values below the boundary are arbitrary. Projecting the compact support onto the tangential coordinates gives a compact set containing the support of the boundary restriction.
-- source:
--   Derived continuity and compact-support lemma used in Hunter, Notes on Partial Differential Equations, Theorem 3.44, printed p. 72, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf. Generalized from smooth to continuous functions and all Lp exponents. Mathlib Continuous.memLp_of_hasCompactSupport, Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.memLp_boundary_of_continuousOn_compact {m : ℕ} (p : ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : ContinuousOn f (closedUpperHalfSpace m))
    (hK : ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∀ x ∈ closedUpperHalfSpace m, x ∉ K → f x = 0) :
    MemLp (fun x' => f (boundaryPoint x')) p volume := by sorry
