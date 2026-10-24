-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_affine_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:59.673752+00:00
-- url     : https://prove2.me/theorems/21b8badb-e824-469b-bfcc-aebd23134345
-- title:
--   Cumulant Transformation Under Affine Maps
-- statement:
--   This formalizes the affine transformation rule for cumulants, corresponding to Bizeul–Klartag–Lehec, Equation (77), p. 19.
--
--   Let $E$ and $F$ be complete finite-dimensional real inner-product spaces with Borel structures. Let $T:E\to F$ be a continuous linear equivalence, let $a\in E$, and let $\mu$ be a finite nonzero measure on $E$. Assume all exponential norm moments of $\mu$ are finite. For $k\geq2$ and directions $u_i\in F$,
--
--   $$
--   \kappa_k^{(T(\cdot-a))_\#\mu}(u_1,\ldots,u_k)
--   =
--   \kappa_k^\mu(T^*u_1,\ldots,T^*u_k).
--   $$
--
--   The pushforward is `Measure.map (fun x => T (x - a)) μ`, and $T^*$ is represented by `ContinuousLinearMap.adjoint`. The translation does not affect cumulants of order at least two.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L885-L975 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section InnerProduct
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_408915f [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (a : E) (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {k : ℕ} (hk : 2 ≤ k) (u : Fin k → F) :
    cumulant (μ.map (fun x => T (x - a))) k u =
      cumulant μ k (fun i => ContinuousLinearMap.adjoint (T : E →L[ℝ] F) (u i)) := by sorry
