-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_add_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:31.035046+00:00
-- url     : https://prove2.me/theorems/2ed3b61d-3daf-4e91-b963-da93092fcaf2
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
--   **Formalization Note** The measure is only assumed finite and nonzero, not necessarily a probability measure. The equality is asserted for every natural-number order $d$ in the finite-dimensional space $E$; the `MemLp` hypotheses use exponent $2$ with respect to $\mu$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_add (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f g : E → ℝ} (hf : MemLp f 2 μ)
--       (hg : MemLp g 2 μ) (d : ℕ) :
--       taylorTensor μ (fun x => f x + g x) d = taylorTensor μ f d + taylorTensor μ g d
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`contDiff_tiltAverage_of_memLp`](https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0), [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82).
--
--   Previous: [`contDiff_tiltAverage_of_memLp`](https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0) · Next: [`taylorTensor_const_mul`](https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959).
--
--   [Source excerpt, lines 360–363](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L360-L363) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L359-L386 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add_readable (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f g : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (d : ℕ) :
    taylorTensor μ (fun x => f x + g x) d = taylorTensor μ f d + taylorTensor μ g d := by sorry
