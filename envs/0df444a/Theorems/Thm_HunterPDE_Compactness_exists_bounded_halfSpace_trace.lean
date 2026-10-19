-- Prove2me | Theorems.Thm_HunterPDE_Compactness_exists_bounded_halfSpace_trace
-- name    : HunterPDE.Compactness.exists_bounded_halfSpace_trace
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:27:24.812176+00:00
-- url     : https://prove2.me/theorems/a50b8f4e-d73a-4da8-86ad-b4d2c5136286
-- title:
--   Bounded half-space trace, with a dimension-independent constant
-- statement:
--   For every finite exponent $1\le p<\infty$, there is a constant $C(p)$, independent of dimension, such that in dimension $m+1$ a trace map is linear up to almost-everywhere equality on $W^{1,p}(\mathbb R^{m+1}_+)$, takes that space into $L^p(\mathbb R^m)$ with norm at most $C(p)$, and agrees with boundary restriction on every smooth function compactly supported on the closed half-space. This is the existence and boundedness part of Hunter Theorem 3.44. The smooth agreement clause does not assume Sobolev membership. The kernel characterization is a separate theorem. The expected proof bounds smooth boundary restriction using normal-line calculus and Hölder, then extends by Theorem 3.42 and completeness of $L^p$.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.exists_bounded_halfSpace_trace (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℕ, ∃ T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g) ∧ (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f) ∧ (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')) := by sorry
