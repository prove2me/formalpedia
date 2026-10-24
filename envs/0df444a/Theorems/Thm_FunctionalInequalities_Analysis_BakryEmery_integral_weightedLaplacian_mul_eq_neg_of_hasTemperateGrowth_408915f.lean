-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:36.14777+00:00
-- url     : https://prove2.me/theorems/93cbc108-5fa3-487b-8792-f6b1176f8b10
-- title:
--   Integration by Parts for Temperate-Growth Functions
-- statement:
--   This formalizes Equation (15) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited as Equation (15), p. 6.
--
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $V,f,g:E\to\mathbb R$. Assume:
--
--   1. $V$ is $C^1$.
--   2. $\|\nabla V(x)\|\le C_V(1+\|x\|)^{k_V}$ for some $C_V\in\mathbb R$ and $k_V\in\mathbb N$.
--   3. Every exponential moment is integrable for $m.\operatorname{tilted}(-V)$.
--   4. $f$ and $g$ have `HasTemperateGrowth`.
--
--   Then
--
--   $$\int (\mathcal L_Vf)g\,d\mu=-\int\langle\nabla f,\nabla g\rangle\,d\mu,
--   \qquad \mu=m.\operatorname{tilted}(-V).$$
--
--   This is the first equality in the temperate-growth integration-by-parts formula and is reusable for weighted diffusion identities.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (15), p. 6 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Temperate.lean#L161-L287 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_408915f {V f g : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-V)) := by sorry
