-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_centeredGradient_zero_of_compact_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:38.105765+00:00
-- url     : https://prove2.me/theorems/acf03322-bdef-4e64-afaa-000238d2d11b
-- title:
--   Raw Cumulant Expansion of a Centered Gradient Quadratic Form
-- statement:
--   This formalizes the raw expansion underlying Equation (74) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited as part of the spatial step of Lemma 4.3.
--
--   Let $E$ be finite-dimensional, let $\mu$ be a probability measure on $E$ with compact support, let $M:E\to E$ be continuous linear, let $m\in\mathbb N$, and let $h:\operatorname{Fin}(m)\to E$. Define
--   $$v(z)=\nabla\Lambda_\mu(z)-\nabla\Lambda_\mu(0),$$
--   where $\Lambda_\mu=\operatorname{logLaplace}(\mu)$. Then
--
--   $$D^m\langle v(z),Mv(z)\rangle\big|_{z=0}[h]
--   =\sum_{q\,:\,\exists i,\ q(i)=\mathrm{true}\ \wedge\ \exists i,\ q(i)=\mathrm{false}}\left\langle \kappa_{|q|+1}(h_q,\cdot),M\kappa_{m-|q|+1}(h_{\neg q},\cdot)\right\rangle,$$
--
--   where `selected` forms the ordered sublists $h_q$ and $h_{\neg q}$, and the sum ranges over Boolean masks selecting both at least one direction and at least one complementary direction.
--
--   This is a deterministic raw Leibniz expansion; it contains no stochastic-process or cumulant-evolution assertion.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18; Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equations (72) and (74), pp. 20–21 (spatial step of the proof of Lemma 4.3). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L60-L146 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
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

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
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

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact_408915f (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → E) :
    iteratedFDeriv ℝ m (fun z : E =>
        ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
          M (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
      ∑ q ∈ (Finset.univ.filter fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false)),
        ⟪cumulantVector (μ : Measure E) (selected h q),
          M (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ := by sorry
