-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_408915f
-- name    : FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:11.687605+00:00
-- url     : https://prove2.me/theorems/a9b3db1b-b0a7-4398-a692-c6b81b93d091
-- title:
--   Strict Covariance Positivity from Full Affine Support
-- statement:
--   This proves strict positivity of the covariance operator under full affine support.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$ such that $\operatorname{id}\in L^2(\mu)$. Assume that the affine support of $\mu$ is all of $E$:
--
--   $$
--   \operatorname{affineSupport}(\mu)=E.
--   $$
--
--   Then every nonzero vector $v\in E$ satisfies
--
--   $$
--   0<\langle \operatorname{Cov}(\mu)v,v\rangle.
--   $$
--
--   Thus the ambient covariance quadratic form is positive definite under the stated support condition.
--
--   The result is useful for obtaining invertibility or coercivity of covariance on a full affine support.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Positivity.lean#L20-L46 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Positivity`, declaration `FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top_408915f (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hfull : Probability.affineSupport μ = ⊤)
    {v : E} (hv : v ≠ 0) : 0 < ⟪Covariance.operator (μ : Measure E) v, v⟫ := by sorry
