-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_comp_sub
-- name    : HunterPDE.Sobolev.iteratedPartial_comp_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:29:55.018242+00:00
-- url     : https://prove2.me/theorems/6ab565db-226b-494a-8eb7-67b262c4a021
-- title:
--   Multi-index chain rule for a translated reflection
-- statement:
--   Let u be a globally smooth real-valued function on Euclidean n-space. Fix a point x and a multi-index alpha. The alpha derivative in y of u(x-y) is (-1) raised to the total order of alpha times (D^alpha u)(x-y). This is an equality of functions in y and requires no support or integrability hypothesis. The proof iterates the chain rule through the coordinate derivative fold. Zero orders and dimension zero are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 3.19 proof (printed p. 55), using Theorem 1.28 (printed pp. 12–13). Derived multi-index calculus interfaces for arbitrary smooth compact kernels; the reflection rule follows the ordinary chain rule.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

open MeasureTheory ContinuousLinearMap HunterPDE.Sobolev
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Sobolev.iteratedPartial_comp_sub {n : ℕ} (α : Fin n → ℕ)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial α (fun y => u (x-y)) =
      fun y => (-1 : ℝ)^(∑ i, α i) * iteratedPartial α u (x-y) := by sorry
