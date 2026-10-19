-- Prove2me | Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_bound
-- name    : HunterPDE.Compactness.smooth_halfSpace_trace_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:50:18.414228+00:00
-- url     : https://prove2.me/theorems/1c543d15-fe05-4e75-8f8e-14f76d2f6f33
-- title:
--   Dimension-independent boundary estimate for smooth half-space functions
-- statement:
--   For every finite exponent $1\le p<\infty$, smooth functions compactly supported on the closed upper half-space have boundary restrictions in $L^p$, and their boundary norm is bounded by $C(p)$ times their first-order Sobolev norm. The constant is uniform in every dimension $m+1$, including $m=0$. No vanishing condition is imposed on the boundary. This is the smooth estimate in the proof of Hunter Theorem 3.44: integrate the normal derivative of $|f|^p$, then apply Fubini and Hölder (with the normal fundamental theorem estimate directly at $p=1$).
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73; bounded-extension lemma generalizes the density-and-continuity step.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.smooth_halfSpace_trace_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℕ,
      ∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        IsSmoothCompactClosedHalfSpace f →
          MemLp (fun x' => f (boundaryPoint x')) p volume ∧
          eLpNorm (fun x' => f (boundaryPoint x')) p volume ≤
            (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f := by sorry
