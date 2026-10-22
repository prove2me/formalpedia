-- Prove2me | Theorems.Thm_JHolomorphic_norm_le_norm_apply_one_add_norm_apply_I
-- name    : JHolomorphic.norm_le_norm_apply_one_add_norm_apply_I
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:25:09.406219+00:00
-- url     : https://prove2.me/theorems/5941f05c-38b4-4f59-8ac3-f340a522c1e2
-- title:
--   The norm of a real-linear map on $\mathbb C$ is at most $\|T1\|+\|Ti\|$
-- statement:
--   Let $F$ be a real normed space and $T:\mathbb C\to F$ a continuous real-linear map. Then
--   $$\|T\|\le\|T(1)\|+\|T(i)\|.$$
--   This bounds operator norms of derivatives on planar domains by their two partial derivatives.
--
--   **Formalization Note** `T : ℂ →L[ℝ] F`, the operator norm `‖T‖`.
-- source:
--   Elementary linear algebra; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- The operator norm of a real-linear map `T` on `ℂ` is at most `‖T 1‖ + ‖T i‖`. -/
theorem norm_le_norm_apply_one_add_norm_apply_I {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℂ →L[ℝ] F) : ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ := by
  sorry

end JHolomorphic
