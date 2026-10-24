-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_sum_variance_entries_eq_integral_trace_sub_trace_mean_408915f
-- name    : FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:21.66942+00:00
-- url     : https://prove2.me/theorems/ec7ffbf6-7013-4bda-a25e-0198a36def4d
-- title:
--   Sum of Matrix Entry Variances as a Trace Difference
-- statement:
--   This is a finite-dimensional random-matrix variance identity.
--
--   Let $\mu$ be a probability measure on a measurable space $\alpha$. Let $H:\alpha\to\mathbb R^{n\times n}$ be almost-everywhere symmetric, with every entry in $L^2(\mu)$, and let $M\in\mathbb R^{n\times n}$ be symmetric. Assume that $M_{ij}=\int H_{ij}(x)\,d\mu(x)$ for every $i,j$. Then
--
--   $$\sum_{i,j}\operatorname{Var}_{\mu}(H_{ij})
--   =\int_\alpha\operatorname{tr}\!\bigl(H(x)H(x)\bigr)\,d\mu(x)-\operatorname{tr}(M^2).$$
--
--   This identity converts entrywise variance sums into trace expressions and is reusable in Hessian and matrix-energy estimates.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Moments.lean#L467-L493 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Moments`, declaration `FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean`; the repository is private at upload time).

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

open MeasureTheory
section MatrixVarianceTrace
open MeasureTheory Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability

theorem FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean_408915f {alpha : Type*} [MeasurableSpace alpha]
    {n : ℕ} (mu : Measure alpha) [IsProbabilityMeasure mu]
    (H : alpha → Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hH : ∀ᵐ x ∂mu, (H x).IsSymm)
    (hH2 : ∀ i j, MemLp (fun x => H x i j) 2 mu)
    (hmean : ∀ i j, (∫ x, H x i j ∂mu) = M i j) :
    (∑ p : Fin n × Fin n, ProbabilityTheory.variance (fun x => H x p.1 p.2) mu) =
      (∫ x, (H x * H x).trace ∂mu) - (M * M).trace := by sorry
