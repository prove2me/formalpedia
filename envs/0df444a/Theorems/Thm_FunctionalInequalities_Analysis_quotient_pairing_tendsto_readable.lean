-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_quotient_pairing_tendsto_readable
-- name    : FunctionalInequalities.Analysis.quotient_pairing_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:28.377931+00:00
-- url     : https://prove2.me/theorems/93835bcb-bdbc-4706-adbe-19b48ce839be
-- title:
--   Difference Quotient Pairing Limit
-- statement:
--   This is a technical difference-quotient limit for an $L^2$ function.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $f\in L^2(\operatorname{vol})$, let $v\in E$, and let $\psi:E\to\mathbb R$ be $C^1$ with compact support. As $t\to0$ through nonzero real values,
--   $$\int_E t^{-1}\bigl(f(x-tv)-f(x)\bigr)\psi(x)\,d\operatorname{vol}(x)
--   \longrightarrow
--   \int_E f(x)\,D\psi(x)[v]\,d\operatorname{vol}(x).$$
--
--   The limit is taken in the punctured neighborhood filter `𝓝[≠] 0`. This identity is an integration-pairing ingredient for extracting weak derivatives from difference quotients.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma quotient_pairing_tendsto {f : E → ℝ}
--       (hf : MemLp f 2 (volume : Measure E)) (v : E)
--       {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
--       Tendsto
--         (fun t : ℝ => ∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x)
--         (𝓝[≠] 0) (𝓝 (∫ x, f x * fderiv ℝ ψ x v))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Mollification`](https://prove2.me/theorems/480cb5f8-8cac-4e12-bd32-870acaf66221).
--
--   Previous: [`fderiv_convolution_eq_of_hasWeakDerivAlong`](https://prove2.me/theorems/21b92288-9077-4db1-9b99-ee62a25b6a04) · Next: [`exists_hasWeakDerivAlong_of_sq_difference_le`](https://prove2.me/theorems/75fca118-0385-4fa0-a865-9c9b02ff0dda).
--
--   [Source excerpt, lines 134–139](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L134-L139) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L134-L184 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Mollification`, declaration `_private.FunctionalInequalities.Analysis.WeakDerivative.Mollification.0.FunctionalInequalities.Analysis.quotient_pairing_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Mollification

open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

lemma FunctionalInequalities.Analysis.quotient_pairing_tendsto_readable {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (v : E)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Tendsto
      (fun t : ℝ => ∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x)
      (𝓝[≠] 0) (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by sorry
