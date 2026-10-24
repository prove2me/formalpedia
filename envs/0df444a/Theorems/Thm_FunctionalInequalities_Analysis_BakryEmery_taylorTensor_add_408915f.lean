-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_add_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:27.652007+00:00
-- url     : https://prove2.me/theorems/05f6e103-5394-4ab8-a98d-a2ab5329a61b
-- title:
--   Additivity of the Taylor Tensor on $L^2(\mu)$
-- statement:
--   This is a technical additivity statement for the Taylor tensor `taylorTensor` associated with tilt averages.
--
--   Let $E$ be a finite-dimensional real inner-product normed additive group equipped with its Borel measurable structure, and let $\mu$ be a finite, nonzero measure on $E$. Assume that:
--
--   1. For every real number $r$, the function $x \mapsto \exp(r\lVert x\rVert)$ is integrable with respect to $\mu$.
--   2. The functions $f,g : E \to \mathbb{R}$ belong to $L^2(\mu)$, expressed in Lean as `MemLp f 2 μ` and `MemLp g 2 μ`.
--   3. $d$ is a natural number.
--
--   Then the Taylor tensor of the pointwise sum $f+g$ is the sum of the individual Taylor tensors:
--
--   $$
--   \operatorname{taylorTensor}_{\mu}(f+g,d)
--   =
--   \operatorname{taylorTensor}_{\mu}(f,d)+\operatorname{taylorTensor}_{\mu}(g,d).
--   $$
--
--   This declaration records the linearity of the Taylor-tensor construction on square-integrable functions and can be reused whenever the stated exponential-moment and $L^2$ hypotheses hold.
--
--   **Formalization Note** The measure is only assumed finite and nonzero, not necessarily a probability measure. The equality is asserted for every natural-number order $d$ in the finite-dimensional space $E; the `MemLp` hypotheses use exponent $2$ with respect to $\mu$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L359-L386 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
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

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
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
section IntegralCalculus
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add_408915f (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f g : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (d : ℕ) :
    taylorTensor μ (fun x => f x + g x) d = taylorTensor μ f d + taylorTensor μ g d := by sorry
