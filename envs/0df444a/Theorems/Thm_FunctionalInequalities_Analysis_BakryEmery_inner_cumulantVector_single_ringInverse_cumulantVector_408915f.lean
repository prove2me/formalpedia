-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_cumulantVector_single_ringInverse_cumulantVector_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:44.926084+00:00
-- url     : https://prove2.me/theorems/e4c5446d-e8c7-4f88-a556-02382bfebaa6
-- title:
--   Singleton Cumulant Allocation Identity
-- statement:
--   This formalizes the singleton allocation identity in Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited at p. 21.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a compactly supported probability measure on $E$. Assume that the covariance operator $A=\operatorname{Cov}(\mu)$ is a unit in the relevant operator ring, so that $A^{-1}$ is available. For every finite list $h_s$ in $E$ and every $w\in E$,
--
--   $$\left\langle \kappa_2(w,\cdot),A^{-1}\kappa_{|h_s|+1}(h_s,\cdot)\right\rangle
--   =\kappa_{|h_s|+1}(h_s,w).$$
--
--   In Lean, the cumulant vectors are represented by `cumulantVector`, the covariance operator by `Covariance.operator`, and the inverse by `Ring.inverse`. The statement is a reusable reduction of a covariance-inverse pairing to a higher cumulant.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L657-L721 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section SingletonAllocation

theorem FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector_408915f (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hA : IsUnit (Covariance.operator (μ : Measure E)))
    (hs : List E) (w : E) :
    ⟪cumulantVector (μ : Measure E) [w],
        Ring.inverse (Covariance.operator (μ : Measure E)) (cumulantVector (μ : Measure E) hs)⟫ =
      cumulant (μ : Measure E) (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by sorry
