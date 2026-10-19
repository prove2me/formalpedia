-- Prove2me | Theorems.Thm_HunterPDE_Compactness_memW0_of_bounded_trace_eq_zero
-- name    : HunterPDE.Compactness.memW0_of_bounded_trace_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:28:13.013716+00:00
-- url     : https://prove2.me/theorems/d27b6dcd-2f18-48ef-9cdb-993967b1bb57
-- title:
--   Zero bounded half-space trace implies approximation by interior test functions
-- statement:
--   Let $1\le p<\infty$. Any bounded trace on the upper half-space that is linear on $W^{1,p}$ up to null sets and agrees with boundary restriction on smooth compact functions has the following property: if $Tf=0$ almost everywhere and $f\in W^{1,p}$, then $f\in W^{1,p}_0$. Here $W^{1,p}_0$ is defined by approximation in the genuine Sobolev norm by smooth functions supported strictly inside the open half-space. No zero-trace characterization is built into that definition. This is the converse kernel inclusion in Hunter Theorem 3.44, outlined on printed p. 73: show zero extension has weak first derivatives, translate into the domain, mollify, and truncate. The trace hypotheses are explicit, so the result applies to any construction of the bounded trace.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.memW0_of_bounded_trace_eq_zero {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0) (T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hlinear : (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g))
    (hbound : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f))
    (hsmooth : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW 1 p (upperHalfSpace m) f)
    (hzero : T f =ᵐ[volume] 0) : MemW0 1 p (upperHalfSpace m) f := by sorry
