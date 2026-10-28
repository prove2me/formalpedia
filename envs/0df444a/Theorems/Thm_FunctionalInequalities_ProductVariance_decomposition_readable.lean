-- Prove2me | Theorems.Thm_FunctionalInequalities_ProductVariance_decomposition_readable
-- name    : FunctionalInequalities.ProductVariance.decomposition_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:12.294303+00:00
-- url     : https://prove2.me/theorems/dd1a36d4-772f-45aa-a604-8df257afcfb1
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.ProductVariance`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem decomposition (hf : MemLp f 2 (μ.prod ν)) :
--       variance f (μ.prod ν) =
--         (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
--         variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ProductVariance`](https://prove2.me/theorems/65fe02bc-71f6-4e5c-8ecc-75b243fe19fa).
--
--   [Source excerpt, lines 104–107](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ProductVariance.lean#L104-L107) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ProductVariance.lean#L101-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ProductVariance`, declaration `FunctionalInequalities.ProductVariance.decomposition`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ProductVariance

open MeasureTheory ProbabilityTheory
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {μ : MeasureTheory.Measure E} {ν : MeasureTheory.Measure F} [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
  {f : E × F → ℝ}

theorem FunctionalInequalities.ProductVariance.decomposition_readable (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
      variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by sorry
