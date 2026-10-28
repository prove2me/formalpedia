-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_const_mul_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_const_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:38.985623+00:00
-- url     : https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959
-- title:
--   Homogeneity of Taylor Tensors
-- statement:
--   This statement proves homogeneity of the Taylor tensor `taylorTensor` under scalar multiplication.
--
--   Let $E$ be a real inner-product space with a measurable structure, let $\mu$ be any measure on $E$, let $c\in\mathbb R$, let $f:E\to\mathbb R$, and let $d\in\mathbb N$. Then
--
--   $$
--   T_d(cf)=c\,T_d f.
--   $$
--
--   This is an algebraic scaling property of the Taylor-tensor construction and is useful for transporting scalar factors through tensor estimates.
--
--   **Formalization Note** No finite-dimensionality, Borel-space, finiteness, integrability, or square-integrability assumptions occur in the statement. Scalar multiplication on the target continuous multilinear map is Lean's `SMul` operation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_const_mul (μ : Measure E) (c : ℝ) (f : E → ℝ) (d : ℕ) :
--       taylorTensor μ (fun x => c * f x) d = c • taylorTensor μ f d
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Previous: [`taylorTensor_add`](https://prove2.me/theorems/2ed3b61d-3daf-4e91-b963-da93092fcaf2) · Next: [`exists_norm_taylorTensor_le`](https://prove2.me/theorems/3b9f7ced-1180-435b-b7cb-81230ca3ce07).
--
--   [Source excerpt, lines 390–391](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L390-L391) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L388-L413 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_const_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]
omit [FiniteDimensional ℝ E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_const_mul_readable (μ : Measure E) (c : ℝ) (f : E → ℝ) (d : ℕ) :
    taylorTensor μ (fun x => c * f x) d = c • taylorTensor μ f d := by sorry
