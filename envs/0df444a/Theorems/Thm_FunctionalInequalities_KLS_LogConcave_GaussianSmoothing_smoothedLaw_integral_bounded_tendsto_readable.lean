-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_integral_bounded_tendsto_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_integral_bounded_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:20.890081+00:00
-- url     : https://prove2.me/theorems/0594eb14-470e-44f6-ba57-66325d98a696
-- title:
--   Weak Convergence of Smoothed Laws on Bounded Continuous Tests
-- statement:
--   This statement proves convergence of bounded continuous test-function integrals under Gaussian smoothing.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $μ$ be a probability measure on $E$, let $ρ : E → ℝ$ satisfy `IsBorellDensity μ volume ρ`, and let $f : E → ℝ$ be a bounded continuous function, represented in Lean by a `BoundedContinuousFunction`. For the smoothed law `smoothedLaw μ s`, as $s\to\text{atTop}$,
--
--   $$
--   \int_E f(y)\,d(\operatorname{smoothedLaw}(μ,s))(y)
--   \longrightarrow
--   \int_E f(y)\,dμ(y).
--   $$
--
--   This is the bounded-continuous-function form of weak convergence for the Gaussian-smoothed laws.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothedLaw_integral_bounded_tendsto {μ : Measure E} [IsProbabilityMeasure μ]
--       {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) (f : BoundedContinuousFunction E ℝ) :
--       Tendsto (fun s : ℝ => ∫ y, f y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y, f y ∂μ))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Approximation`](https://prove2.me/theorems/d5560108-f34d-426e-87a5-851045a6e923).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548).
--
--   Supporting theorems: [`normalizedDensity_tendsto_L1`](https://prove2.me/theorems/c0a6720b-acb6-4b57-b8ed-118a32ffd64b).
--
--   Previous: [`normalizedDensity_tendsto_L1`](https://prove2.me/theorems/c0a6720b-acb6-4b57-b8ed-118a32ffd64b).
--
--   [Source excerpt, lines 307–309](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Approximation.lean#L307-L309) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Approximation.lean#L305-L340 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_integral_bounded_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation

set_option autoImplicit false
open MeasureTheory Set Filter Topology Bornology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_integral_bounded_tendsto_readable {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) (f : BoundedContinuousFunction E ℝ) :
    Tendsto (fun s : ℝ => ∫ y, f y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y, f y ∂μ)) := by sorry
