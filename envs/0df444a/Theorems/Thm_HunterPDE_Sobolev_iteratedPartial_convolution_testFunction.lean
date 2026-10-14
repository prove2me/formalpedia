-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_convolution_testFunction
-- name    : HunterPDE.Sobolev.iteratedPartial_convolution_testFunction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:28:59.09299+00:00
-- url     : https://prove2.me/theorems/4da4408b-0121-4f93-b345-dda4fdd2cf6b
-- title:
--   Multi-index differentiation of convolution with a test function
-- statement:
--   Let u be a smooth compactly supported scalar function on Euclidean n-space and let f be locally integrable. For every multi-index alpha, the classical ordered multi-index derivative of u*f equals (D^alpha u)*f, as an equality of functions. No global integrability, positivity or normalization is assumed. The proof iterates compact-kernel differentiation under the integral, with compact support and smoothness preserved at every step. All derivative orders and dimension zero are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 3.19 proof (printed p. 55), using Theorem 1.28 (printed pp. 12–13). Derived multi-index calculus interfaces for arbitrary smooth compact kernels; the reflection rule follows the ordinary chain rule.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Ring

open MeasureTheory ContinuousLinearMap HunterPDE.Sobolev
open scoped Convolution ContDiff
set_option autoImplicit false

theorem HunterPDE.Sobolev.iteratedPartial_convolution_testFunction {n : ℕ} (α : Fin n → ℕ)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (hf : LocallyIntegrable f) :
    iteratedPartial α (u ⋆[lsmul ℝ ℝ, volume] f) =
      (iteratedPartial α u ⋆[lsmul ℝ ℝ, volume] f) := by sorry
