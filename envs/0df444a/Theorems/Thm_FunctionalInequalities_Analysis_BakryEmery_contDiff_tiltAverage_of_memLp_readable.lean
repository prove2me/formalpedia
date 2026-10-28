-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:02.579665+00:00
-- url     : https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0
-- title:
--   Smoothness of Tilt Averages of $L^2$ Functions
-- statement:
--   This formalizes the smoothness part of the tilt-average framework in Bizeul–Klartag–Lehec, Equations (26)–(28), p. 9.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $\mu$ be a finite nonzero measure, and assume every exponential norm moment is finite:
--
--   $$
--   \forall r\in\mathbb R,
--   \quad \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   For any real-valued $f\in L^2(\mu)$, the tilt average
--
--   $$
--   F_f(z)=\int f(x)\,d\mu_z(x)
--   $$
--
--   is smooth on all of $E$:
--
--   $$
--   F_f\in C^\infty(E).
--   $$
--
--   Here `tiltAverage μ f` is defined using the exponentially tilted measure. The conclusion is global smoothness, not merely smoothness near the origin.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_tiltAverage_of_memLp (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ) :
--       ContDiff ℝ ∞ (tiltAverage μ f)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82).
--
--   Previous: [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82) · Next: [`taylorTensor_add`](https://prove2.me/theorems/2ed3b61d-3daf-4e91-b963-da93092fcaf2).
--
--   [Source excerpt, lines 304–306](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L304-L306) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equations (26)–(28), p. 9 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L303-L357 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_readable (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ) :
    ContDiff ℝ ∞ (tiltAverage μ f) := by sorry
