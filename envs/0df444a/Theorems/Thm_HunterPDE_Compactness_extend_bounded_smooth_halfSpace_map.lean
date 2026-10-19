-- Prove2me | Theorems.Thm_HunterPDE_Compactness_extend_bounded_smooth_halfSpace_map
-- name    : HunterPDE.Compactness.extend_bounded_smooth_halfSpace_map
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:50:30.333667+00:00
-- url     : https://prove2.me/theorems/b5fb9e21-b3a2-4c20-8a5c-2b95975439ec
-- title:
--   Extend a bounded smooth half-space map to Sobolev functions
-- statement:
--   Let $1\le p<\infty$, let $k,m,d$ be arbitrary natural numbers, and assume smooth functions compactly supported on the closed upper half-space are dense in $W^{k,p}$. Any map from these smooth functions into $L^p(\mathbb R^d)$ that is linear up to almost-everywhere equality and bounded by $C$ times the Sobolev norm extends to a map on Sobolev functions with the same linearity and bound. The extension agrees with the original map on every smooth function in this class. Both maps are represented on all raw functions; their values outside the stated classes are immaterial. This is the bounded-extension step used in Hunter Theorem 3.44, generalized to arbitrary Sobolev order and output dimension. The intended proof takes limits of images of smooth approximants in the complete space $L^p$, proves independence of approximants from the bound, and passes linearity and the bound to the limit. It must handle zero Sobolev distance and arbitrary representatives explicitly.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73; bounded-extension lemma generalizes the density-and-continuity step.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.extend_bounded_smooth_halfSpace_map {m k d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0)
    (R : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hdense : ∀ f, MemW k p (upperHalfSpace m) f →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ φ, IsSmoothCompactClosedHalfSpace φ ∧
        sobolevNorm k p (upperHalfSpace m) (f - φ) < ε)
    (hlinear : ∀ f g, IsSmoothCompactClosedHalfSpace f →
      IsSmoothCompactClosedHalfSpace g → ∀ a b : ℝ,
        R (a • f + b • g) =ᵐ[volume] a • R f + b • R g)
    (hbound : ∀ f, IsSmoothCompactClosedHalfSpace f →
      MemLp (R f) p volume ∧ eLpNorm (R f) p volume ≤
        (C : ℝ≥0∞) * sobolevNorm k p (upperHalfSpace m) f) :
    ∃ T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ f g, MemW k p (upperHalfSpace m) f → MemW k p (upperHalfSpace m) g →
        ∀ a b : ℝ, T (a • f + b • g) =ᵐ[volume] a • T f + b • T g) ∧
      (∀ f, MemW k p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧ eLpNorm (T f) p volume ≤
          (C : ℝ≥0∞) * sobolevNorm k p (upperHalfSpace m) f) ∧
      (∀ f, IsSmoothCompactClosedHalfSpace f → T f =ᵐ[volume] R f) := by sorry
