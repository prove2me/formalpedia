-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_normalizedDensity_tendsto_L1_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:21.003128+00:00
-- url     : https://prove2.me/theorems/c0a6720b-acb6-4b57-b8ed-118a32ffd64b
-- title:
--   L¹ Convergence of Normalized Gaussian Smoothing
-- statement:
--   This statement proves convergence in $L^1$ of normalized Gaussian smoothing to its source density.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $ν$ be a probability measure on $V$, and let $ρ : V → ℝ$ satisfy `IsBorellDensity ν volume ρ`. For each real parameter $s$, let `normalizedDensity ρ s` denote the normalized Gaussian-smoothed density. As $s$ tends to infinity through the real numbers,
--
--   $$
--   \int_V \left|\operatorname{normalizedDensity}(ρ,s,x)-ρ(x)\right|\,dx
--   \longrightarrow 0.
--   $$
--
--   The result supplies total-variation-type approximation at the density level and can be reused to compare integrals of bounded observables.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem normalizedDensity_tendsto_L1 {ν : Measure V}
--       [IsProbabilityMeasure ν] {ρ : V → ℝ}
--       (hρ : IsBorellDensity ν volume ρ) :
--       Tendsto (fun s : ℝ => ∫ x : V, |normalizedDensity ρ s x - ρ x|)
--         atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Approximation`](https://prove2.me/theorems/d5560108-f34d-426e-87a5-851045a6e923).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548).
--
--   Supporting theorems: [`ae_continuous`](https://prove2.me/theorems/478771a1-189a-4be0-959d-cfd95147cfff).
--
--   Next: [`smoothedLaw_integral_bounded_tendsto`](https://prove2.me/theorems/0594eb14-470e-44f6-ba57-66325d98a696).
--
--   [Source excerpt, lines 187–191](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Approximation.lean#L187-L191) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Approximation.lean#L184-L222 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation

set_option autoImplicit false
open MeasureTheory Set Filter Topology Bornology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1_readable {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    Tendsto (fun s : ℝ => ∫ x : V, |normalizedDensity ρ s x - ρ x|)
      atTop (𝓝 0) := by sorry
