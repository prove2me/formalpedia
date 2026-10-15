-- Prove2me | Theorems.Thm_MeasureTheory_ofReal_abs_sub_le_segment_lintegral_gradient
-- name    : MeasureTheory.ofReal_abs_sub_le_segment_lintegral_gradient
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T07:19:15.377692+00:00
-- url     : https://prove2.me/theorems/887df531-1bde-458b-ab87-634ab458570e
-- title:
--   C1 displacement bounded by the gradient integrated along a segment
-- statement:
--   Let $E$ be a real Hilbert space and let $f:E\to\mathbb R$ be $C^1$. For all $x,z\in E$,
--
--   $$|f(x)-f(z)|\le \|z-x\|\int_0^1\|\nabla f(x+t(z-x))\|\,dt.$$
--
--   The statement uses nonnegative extended integrals, so it is also suitable for Tonelli arguments. It follows from the fundamental theorem of calculus on the affine segment and the inner-product inequality. The Hilbert-space formulation generalizes the Euclidean calculation in the source.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 68–69 (PDF pp. 74–75), proof of Theorem 3.36, equation (3.14). The segment calculation is parametrized on [0,1] and extended to real Hilbert spaces.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
set_option autoImplicit false

theorem MeasureTheory.ofReal_abs_sub_le_segment_lintegral_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x z : E) :
    ENNReal.ofReal |f x - f z| ≤ ENNReal.ofReal ‖z - x‖ *
      (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖gradient f (x + t • (z - x))‖) := by sorry
