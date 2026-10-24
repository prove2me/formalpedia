-- Prove2me | Theorems.Thm_FunctionalInequalities_ProductVariance_decomposition_408915f
-- name    : FunctionalInequalities.ProductVariance.decomposition_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:20.094257+00:00
-- url     : https://prove2.me/theorems/44cf63ed-98a5-40b3-80b2-0253ef19b2ac
-- title:
--   Product Measure Variance Decomposition
-- statement:
--   This is the law of total variance for a product probability measure.
--
--   Let $\mu$ and $\nu$ be probability measures on measurable spaces $E$ and $F$, and let $f:E\times F\to\mathbb R$ belong to $L^2(\mu\otimes\nu)$. Then
--
--   $$\operatorname{Var}_{\mu\otimes\nu}(f)
--   =\int_E\operatorname{Var}_{\nu}\bigl(y\mapsto f(x,y)\bigr)\,d\mu(x)
--   +\operatorname{Var}_{\mu}\!\left(x\mapsto\int_F f(x,y)\,d\nu(y)\right).$$
--
--   The explicit `MemLp f 2` assumption supplies the iterated integrability needed for the ordinary integral formulation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ProductVariance.lean#L101-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ProductVariance`, declaration `FunctionalInequalities.ProductVariance.decomposition`; the repository is private at upload time).

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.ProductVariance
end FunctionalInequalities.ProductVariance
open FunctionalInequalities FunctionalInequalities.ProductVariance
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : E × F → ℝ}

theorem FunctionalInequalities.ProductVariance.decomposition_408915f (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
      variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by sorry
