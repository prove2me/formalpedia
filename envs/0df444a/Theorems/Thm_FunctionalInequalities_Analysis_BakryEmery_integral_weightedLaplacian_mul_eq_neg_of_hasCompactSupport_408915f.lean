-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:31.917411+00:00
-- url     : https://prove2.me/theorems/ebd41df3-0650-47d6-867c-6c829e29ed2c
-- title:
--   Compactly Supported Integration by Parts
-- statement:
--   This is the compactly supported integration-by-parts identity for the weighted Laplacian.
--
--   Let $E$ be finite-dimensional, complete, and equipped with a real inner product; let $m$ be an additive Haar measure; and let $V,f,w:E\to\mathbb R$. Assume that $V$ is $C^1$, $f$ and $w$ are $C^2$, and $w$ has compact support. Then
--
--   $$\int (\mathcal L_Vf)(x)w(x)\,d\bigl(m.\operatorname{tilted}(-V)\bigr)(x)
--   =-\int\langle\nabla f(x),\nabla w(x)\rangle\,d\bigl(m.\operatorname{tilted}(-V)\bigr)(x).$$
--
--   Here `weightedLaplacian V f` is $\mathcal L_Vf$. The result is the compact-support form of the first integration-by-parts equality.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Temperate.lean#L25-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_408915f {V f w : E → ℝ}
    (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 2 f) (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    ∫ x, weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V)) := by sorry
