-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_one_apply_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:32.607475+00:00
-- url     : https://prove2.me/theorems/5f1e7c9b-800d-4d4b-84f5-1fa20ecda112
-- title:
--   First Taylor Tensor as a Centered Moment
-- statement:
--   This formalizes the centered first-moment formula for the first Taylor tensor.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$. Assume:
--
--   1. For every $r\in\mathbb R$, $x\mapsto e^{r\|x\|}$ is integrable with respect to $\mu$.
--   2. $f:E\to\mathbb R$ belongs to $L^2(\mu)$.
--   3. $w\in E$.
--
--   Writing $T_d f$ for `taylorTensor μ f d`, the first tensor evaluated at $w$ satisfies
--
--   $$
--   T_1f(w)=\int \langle w,x\rangle f(x)\,d\mu(x)
--   -\left(\int f\,d\mu\right)\left(\int \langle w,x\rangle\,d\mu(x)\right).
--   $$
--
--   This identifies the first Taylor tensor with the centered first moment and provides the degree-one case used in tensor and cumulant calculations.
--
--   **Formalization Note** The measure is a probability measure, and all displayed integrals are ordinary real-valued integrals under the stated integrability consequences of the hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_one_apply (μ : Measure E) [IsProbabilityMeasure μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ}
--       (hf : MemLp f 2 μ) (w : E) :
--       taylorTensor μ f 1 (fun _ => w) =
--         (∫ x, ⟪w, x⟫ * f x ∂μ) - (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/LocalDerivatives`](https://prove2.me/theorems/62e3d2e2-1b96-4afe-b27b-faf9f7826a95).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`contDiff_tiltAverage_of_memLp`](https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0), [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82).
--
--   [Source excerpt, lines 168–172](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/LocalDerivatives.lean#L168-L172) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/LocalDerivatives.lean#L166-L257 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) (w : E) :
    taylorTensor μ f 1 (fun _ => w) =
      (∫ x, ⟪w, x⟫ * f x ∂μ) - (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ := by sorry
