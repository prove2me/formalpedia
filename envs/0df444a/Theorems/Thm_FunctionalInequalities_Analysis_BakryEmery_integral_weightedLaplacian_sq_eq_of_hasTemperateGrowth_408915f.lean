-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:43.4745+00:00
-- url     : https://prove2.me/theorems/d9471d4e-59ed-4781-be0f-dba8d854988a
-- title:
--   Integrated Bochner Formula
-- statement:
--   This formalizes Equation (16) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited as Equation (16), p. 6.
--
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $V,f:E\to\mathbb R$. Assume that $V$ and $f$ have `HasTemperateGrowth`, and that every exponential moment is integrable for $\mu=m.\operatorname{tilted}(-V)$. Then
--
--   $$\int (\mathcal L_Vf)^2\,d\mu
--   =\int \|D^2f\|_{\mathrm{HS}}^2\,d\mu
--   +\int D^2V[\nabla f,\nabla f]\\,d\mu.$$
--
--   In the formalization, `hessianSqStdBasis f` represents the squared Hessian Hilbert–Schmidt norm in the standard orthonormal basis, while `bilinearIteratedFDerivTwo` represents the Hessian bilinear form. This is the integrated Bochner identity on the temperate-growth class.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (16), p. 6 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L187-L215 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_408915f {V f : E → ℝ}
    (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) =
      ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) +
        ∫ x, bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) ∂(m.tilted (-V)) := by sorry
