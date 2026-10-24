-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_letwinQuadraticBound_of_tendsto_moments_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:29.678985+00:00
-- url     : https://prove2.me/theorems/aeb4a116-2160-42ee-a1cb-838766ea95f2
-- title:
--   Stability of the Quadratic Bound Under Moment Convergence
-- statement:
--   This formalizes the limiting assertion in Lemma A.1 of Letwin (arXiv:2607.24164v1).
--
--   Let $(\mu_k)_{k\in\mathbb N}$ and $\nu$ be probability measures on a finite-dimensional real inner-product space $E$. Assume:
--
--   1. Each identity map belongs to $L^4(\mu_k)$ and to $L^4(\nu)$.
--   2. For every $d\le4$ and every $v:\operatorname{Fin}(d)\to E$, the mixed moments converge:
--      $$\int\prod_i\langle v_i,x\rangle\,d\mu_k(x)\longrightarrow\int\prod_i\langle v_i,x\rangle\,d\nu(x).$$
--   3. Every $\mu_k$ satisfies `LetwinQuadraticBound`.
--
--   Then $\nu$ also satisfies `LetwinQuadraticBound`.
--
--   The result supplies closure of the quadratic-form estimate under convergence of moments through degree four.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.1. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L1055-L1131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments`; the repository is private at upload time).

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
section MomentLimit
open ProbabilityTheory Filter Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments_408915f [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : ℕ → Measure E) (ν : Measure E) [∀ k, IsProbabilityMeasure (μ k)]
    [IsProbabilityMeasure ν] (hμ : ∀ k, MemLp id 4 (μ k)) (hν : MemLp id 4 ν)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(μ k)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂ν)))
    (hL : ∀ k, LetwinQuadraticBound (μ k)) : LetwinQuadraticBound ν := by sorry
