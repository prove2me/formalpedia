-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:38.833528+00:00
-- url     : https://prove2.me/theorems/cf9e012f-9f9d-42cc-b907-210977547e69
-- title:
--   Polynomial Growth Implies Integrability
-- statement:
--   This theorem gives integrability of a vector-valued function under all exponential moments.
--
--   Let $E$ be a measurable normed space, let $F$ be a normed additive group, and let $\mu$ be a measure such that $e^{r\|x\|}$ is integrable for every $r\in\mathbb R$. Suppose that $g:E\to F$ is strongly measurable almost everywhere and that, for some $C\in\mathbb R$ and $k\in\mathbb N$,
--
--   $$\|g(x)\|\le C(1+\|x\|)^k\qquad\text{for every }x\in E.$$
--
--   Then $g$ is integrable with respect to $\mu$. The result is a general domination lemma for polynomially bounded functions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L224-L263 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow`; the repository is private at upload time).

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
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
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
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_408915f {F : Type*} [NormedAddCommGroup F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable g μ := by sorry
