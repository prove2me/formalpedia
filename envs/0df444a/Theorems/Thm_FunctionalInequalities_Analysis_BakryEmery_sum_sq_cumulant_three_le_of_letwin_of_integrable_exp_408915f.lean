-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:41.205735+00:00
-- url     : https://prove2.me/theorems/021e20d8-43da-4974-acd0-954b165a7701
-- title:
--   Third Cumulant Contraction Bound
-- statement:
--   This is the local-moment form of Lemma 4.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be a probability measure on a finite-dimensional real inner-product space $E$. Assume:
--
--   1. $r>0$ and $e^{r\|x\|}$ is integrable with respect to $\mu$.
--   2. $\mu$ is centered: $\int\langle v,x\rangle\,d\mu(x)=0$ for every $v\in E$.
--   3. $\mu$ is isotropic: $\int\langle v,x\rangle\langle w,x\rangle\,d\mu(x)=\langle v,w\rangle$.
--   4. $\mu$ satisfies `LetwinQuadraticBound`.
--
--   Then for every $u\in E$, with $e_j$ the standard orthonormal basis,
--
--   $$\sum_{j,k}\kappa_3(u,e_j,e_k)^2\le 8\|u\|^2.$$
--
--   This is the Hilbert–Schmidt contraction estimate for the third cumulant under the stated local exponential-moment assumptions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L229-L333 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_408915f (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by sorry
