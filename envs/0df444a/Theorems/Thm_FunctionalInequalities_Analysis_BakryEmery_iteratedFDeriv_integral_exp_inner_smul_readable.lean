-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_integral_exp_inner_smul_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:00.60917+00:00
-- url     : https://prove2.me/theorems/5c6a3c00-e76c-4094-bd9b-db3f77cc3227
-- title:
--   Derivatives of Exponential Laplace-Type Integrals
-- statement:
--   This theorem identifies the iterated derivatives of a vector-valued Laplace-type integral with weighted moments.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $F$ be a complete real normed space, and let $\mu$ be a measure on $E$. Let $g:E\to F$ be strongly measurable almost everywhere with respect to $\mu$, and assume that for every $r\in\mathbb R$ the function $x\mapsto e^{r\|x\|}\|g(x)\|$ is integrable. For every $d\in\mathbb N$, $z\in E$, and $h:\operatorname{Fin}(d)\to E$, define $N(z)=\int e^{\langle z,x\rangle}g(x)\,d\mu(x)$.
--
--   $$D^dN(z)[h]=\int e^{\langle z,x\rangle}\left(\prod_{j} \langle x,h(j)\rangle\right)g(x)\,d\mu(x).$$
--
--   The result is a reusable differentiation-under-the-integral statement for exponential moments with values in a complete normed space.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_integral_exp_inner_smul (μ : Measure E) {g : E → F}
--       (hg : AEStronglyMeasurable g μ)
--       (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (d : ℕ) (z : E)
--       (h : Fin d → E) :
--       iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) z h =
--         ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Next: [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82).
--
--   [Source excerpt, lines 185–190](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L185-L190) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L184-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul_readable (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (d : ℕ) (z : E)
    (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) z h =
      ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by sorry
