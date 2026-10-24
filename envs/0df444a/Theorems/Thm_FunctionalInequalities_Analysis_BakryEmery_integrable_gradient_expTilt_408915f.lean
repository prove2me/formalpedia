-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_gradient_expTilt_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:44.389492+00:00
-- url     : https://prove2.me/theorems/925a073c-2917-435c-9780-0f2b58f8f866
-- title:
--   Integrability of Compactly Supported Gradients Under Tilting
-- statement:
--   This theorem establishes integrability of the gradient of a compactly supported function under every exponential tilt.
--
--   Let $E$ be a finite-dimensional complete real inner-product space, let $m$ be a measure on $E$, and let $V,f:E\to\mathbb R$. If $f$ is $C^2$ and has compact support, then for every $z\in E$,
--
--   $$\nabla f\in L^1\!\left(\operatorname{expTilt}\bigl(m.\operatorname{tilted}(-V),z\bigr)\right).$$
--
--   No regularity or integrability hypothesis on $V$ is present in the type. This is a technical ingredient for integration by parts and tilt-average identities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L119-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
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
open MeasureTheory FunctionalInequalities.Analysis.Tensor
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
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_408915f {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (z : E) : Integrable (gradient f) (expTilt (m.tilted (-V)) z) := by sorry
