-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_exists_norm_coordTensor_taylorTensor_le_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:43.153998+00:00
-- url     : https://prove2.me/theorems/53066c67-d36a-4271-b230-30d5911326bf
-- title:
--   Coordinate-Norm Bound for Taylor Tensors
-- statement:
--   This is a coordinate-norm continuity estimate for Taylor tensors.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a probability measure on $E$, and assume that $e^{r\|x\|}$ is $\mu$-integrable for every $r\in\mathbb R$. For an integer $n$, an orthonormal basis $b$ indexed by $\operatorname{Fin}(n)$, and an order $d\in\mathbb N$, there exists $C\in\mathbb R$ such that every $f:E\to\mathbb R$ with $f\in L^2(\mu)$ satisfies
--
--   $$\|\operatorname{coordTensor}(b,T_d f)\|\le C\,(eLpNorm(f,2,\mu)).toReal.$$
--
--   The definition `coordTensor` uses the chosen basis and `taylorTensor` denotes $T_d f$. This statement transfers the fixed-order $L^2$ bound to the Hilbert–Schmidt norm of the coefficient array.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L557-L574 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_408915f (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ →
      ‖coordTensor b (taylorTensor μ f d)‖ ≤ C * (eLpNorm f 2 μ).toReal := by sorry
