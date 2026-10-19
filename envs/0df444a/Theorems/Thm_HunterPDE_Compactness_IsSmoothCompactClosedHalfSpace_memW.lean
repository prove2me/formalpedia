-- Prove2me | Theorems.Thm_HunterPDE_Compactness_IsSmoothCompactClosedHalfSpace_memW
-- name    : HunterPDE.Compactness.IsSmoothCompactClosedHalfSpace.memW
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:03:39.973417+00:00
-- url     : https://prove2.me/theorems/d3734142-72d5-4942-85f2-afc56796ea41
-- title:
--   Smooth compact closed-half-space functions belong to every finite-order Sobolev space
-- statement:
--   A function smooth up to the boundary of the closed upper half-space and vanishing there outside a compact set belongs to $W^{k,p}$ of the open upper half-space for every natural order $k$ and finite exponent $1\le p<\infty$. Values outside the closed half-space are arbitrary. Classical derivatives on the interior provide the weak derivatives; smoothness up to the boundary and compact support make those derivatives bounded and integrable. The assertion includes order zero and dimension one.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definitions 3.2 and 3.23 and the smooth class in Theorem 3.42, printed pp.47–48,58–59,72.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.Analysis.Seminorm
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.IsSmoothCompactClosedHalfSpace.memW {m k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) : MemW k p (upperHalfSpace m) f := by sorry
